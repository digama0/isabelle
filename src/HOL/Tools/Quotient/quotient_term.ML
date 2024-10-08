(*  Title:      HOL/Tools/Quotient/quotient_term.ML
    Author:     Cezary Kaliszyk and Christian Urban

Constructs terms corresponding to goals from lifting theorems to
quotient types.
*)

signature QUOTIENT_TERM =
sig
  exception LIFT_MATCH of string

  datatype flag = AbsF | RepF

  val absrep_fun: Proof.context -> flag -> typ * typ -> term
  val absrep_fun_chk: Proof.context -> flag -> typ * typ -> term

  (* Allows Nitpick to represent quotient types as single elements from raw type *)
  val absrep_const_chk: Proof.context -> flag -> string -> term

  val equiv_relation: Proof.context -> typ * typ -> term
  val equiv_relation_chk: Proof.context -> typ * typ -> term

  val get_rel_from_quot_thm: thm -> term
  val prove_quot_thm: Proof.context -> typ * typ -> thm

  val regularize_trm: Proof.context -> term * term -> term
  val regularize_trm_chk: Proof.context -> term * term -> term

  val inj_repabs_trm: Proof.context -> term * term -> term
  val inj_repabs_trm_chk: Proof.context -> term * term -> term

  val derive_qtyp: Proof.context -> typ list -> typ -> typ
  val derive_qtrm: Proof.context -> typ list -> term -> term
  val derive_rtyp: Proof.context -> typ list -> typ -> typ
  val derive_rtrm: Proof.context -> typ list -> term -> term
end;

structure Quotient_Term: QUOTIENT_TERM =
struct

exception LIFT_MATCH of string



(*** Aggregate Rep/Abs Function ***)


(* The flag RepF is for types in negative position; AbsF is for types
   in positive position. Because of this, function types need to be
   treated specially, since there the polarity changes.
*)

datatype flag = AbsF | RepF

fun negF AbsF = RepF
  | negF RepF = AbsF

fun is_identity \<^Const_>\<open>id _\<close> = true
  | is_identity _ = false

fun mk_fun_compose flag (trm1, trm2) =
  case flag of
    AbsF => Const (\<^const_name>\<open>comp\<close>, dummyT) $ trm1 $ trm2
  | RepF => Const (\<^const_name>\<open>comp\<close>, dummyT) $ trm2 $ trm1

fun get_mapfun_data ctxt s =
  (case Symtab.lookup (Functor.entries ctxt) s of
    SOME [map_data] => (case try dest_Const_name (#mapper map_data) of
      SOME c => (Const (c, dummyT), #variances map_data)
    | NONE => raise LIFT_MATCH ("map function for type " ^ quote s ^ " is not a constant."))
  | SOME _ => raise LIFT_MATCH ("map function for type " ^ quote s ^ " is non-singleton entry.")
  | NONE => raise LIFT_MATCH ("No map function for type " ^ quote s ^ " found.")) 

fun defined_mapfun_data ctxt = Symtab.defined (Functor.entries ctxt)

(* looks up the (varified) rty and qty for
   a quotient definition
*)
fun get_rty_qty ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    (case Quotient_Info.lookup_quotients_global thy s of
      SOME {rtyp, qtyp, ...} => (rtyp, qtyp)
    | NONE => raise LIFT_MATCH ("No quotient type " ^ quote s ^ " found."))
  end

(* matches a type pattern with a type *)
fun match ctxt err ty_pat ty =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Sign.typ_match thy (ty_pat, ty) Vartab.empty
      handle Type.TYPE_MATCH => err ctxt ty_pat ty
  end

(* produces the rep or abs constant for a qty *)
fun absrep_const ctxt flag qty_str =
  let
    (* FIXME *)
    fun mk_dummyT (Const (c, _)) = Const (c, dummyT)
      | mk_dummyT (Free (c, _)) = Free (c, dummyT)
      | mk_dummyT _ = error "Expecting abs/rep term to be a constant or a free variable"     
  in
    (case Quotient_Info.lookup_abs_rep ctxt qty_str of
      SOME {abs, rep} => mk_dummyT (case flag of AbsF => abs | RepF => rep)
    | NONE => error ("No abs/rep terms for " ^ quote qty_str))
  end
  
(* Lets Nitpick represent elements of quotient types as elements of the raw type *)
fun absrep_const_chk ctxt flag qty_str =
  Syntax.check_term ctxt (absrep_const ctxt flag qty_str)

fun absrep_match_err ctxt ty_pat ty =
  let
    val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
    val ty_str = Syntax.string_of_typ ctxt ty
  in
    raise LIFT_MATCH (space_implode " "
      ["absrep_fun (Types ", quote ty_pat_str, "and", quote ty_str, " do not match.)"])
  end


(** generation of an aggregate absrep function **)

(* - In case of equal types we just return the identity.

   - In case of TFrees we also return the identity.

   - In case of function types we recurse taking
     the polarity change into account.

   - If the type constructors are equal, we recurse for the
     arguments and build the appropriate map function.

   - If the type constructors are unequal, there must be an
     instance of quotient types:

       - we first look up the corresponding rty_pat and qty_pat
         from the quotient definition; the arguments of qty_pat
         must be some distinct TVars
       - we then match the rty_pat with rty and qty_pat with qty;
         if matching fails the types do not correspond -> error
       - the matching produces two environments; we look up the
         assignments for the qty_pat variables and recurse on the
         assignments
       - we prefix the aggregate map function for the rty_pat,
         which is an abstraction over all type variables
       - finally we compose the result with the appropriate
         absrep function in case at least one argument produced
         a non-identity function /
         otherwise we just return the appropriate absrep
         function

     The composition is necessary for types like

        ('a list) list / ('a foo) foo

     The matching is necessary for types like

        ('a * 'a) list / 'a bar

     The test is necessary in order to eliminate superfluous
     identity maps.
*)

fun absrep_fun ctxt flag (rty, qty) =
  let
    fun absrep_args tys tys' variances =
      let
        fun absrep_arg (types, (_, variant)) =
          (case variant of
            (false, false) => []
          | (true, false) => [(absrep_fun ctxt flag types)]
          | (false, true) => [(absrep_fun ctxt (negF flag) types)]
          | (true, true) => [(absrep_fun ctxt flag types),(absrep_fun ctxt (negF flag) types)])
      in
        maps absrep_arg ((tys ~~ tys') ~~ variances)
      end
    fun test_identities tys rtys' s s' =
      let
        val args = map (absrep_fun ctxt flag) (tys ~~ rtys')
      in
        if forall is_identity args
        then 
          absrep_const ctxt flag s'
        else 
          raise LIFT_MATCH ("No map function for type " ^ quote s ^ " found.")
      end
  in
    if rty = qty
    then \<^Const>\<open>id rty\<close>
    else
      case (rty, qty) of
        (Type (s, tys), Type (s', tys')) =>
          if s = s'
          then
            let
              val (map_fun, variances) = get_mapfun_data ctxt s
              val args = absrep_args tys tys' variances
            in
              list_comb (map_fun, args)
            end
          else
            let
              val (Type (_, rtys), qty_pat) = get_rty_qty ctxt s'
              val qtyenv = match ctxt absrep_match_err qty_pat qty
              val rtys' = map (Envir.subst_type qtyenv) rtys
            in
              if not (defined_mapfun_data ctxt s)
              then
                (*
                    If we don't know a map function for the raw type,
                    we are not necessarilly in troubles because
                    it can still be the case we don't need the map 
                    function <=> all abs/rep functions are identities.
                *)
                test_identities tys rtys' s s'
              else
                let
                  val (map_fun, variances) = get_mapfun_data ctxt s
                  val args = absrep_args tys rtys' variances
                in
                  if forall is_identity args
                  then absrep_const ctxt flag s'
                  else
                    let
                      val result = list_comb (map_fun, args)
                    in
                      mk_fun_compose flag (absrep_const ctxt flag s', result)
                    end
                end
            end
      | (TFree x, TFree x') =>
          if x = x'
          then \<^Const>\<open>id rty\<close>
          else raise (LIFT_MATCH "absrep_fun (frees)")
      | (TVar _, TVar _) => raise (LIFT_MATCH "absrep_fun (vars)")
      | _ => raise (LIFT_MATCH "absrep_fun (default)")
  end

fun absrep_fun_chk ctxt flag (rty, qty) =
  absrep_fun ctxt flag (rty, qty)
  |> Syntax.check_term ctxt



(*** Aggregate Equivalence Relation ***)


(* works very similar to the absrep generation,
   except there is no need for polarities
*)

(* instantiates TVars so that the term is of type ty *)
fun force_typ ctxt trm ty =
  let
    val thy = Proof_Context.theory_of ctxt
    val trm_ty = fastype_of trm
    val ty_inst = Sign.typ_match thy (trm_ty, ty) Vartab.empty
  in
    map_types (Envir.subst_type ty_inst) trm
  end

fun is_eq \<^Const_>\<open>HOL.eq _\<close> = true
  | is_eq _ = false

fun mk_rel_compose (trm1, trm2) =
  Const (\<^const_abbrev>\<open>rel_conj\<close>, dummyT) $ trm1 $ trm2

fun get_relmap ctxt s =
  (case Quotient_Info.lookup_quotmaps ctxt s of
    SOME {relmap, ...} => Const (relmap, dummyT)
  | NONE => raise LIFT_MATCH ("get_relmap (no relation map function found for type " ^ s ^ ")"))

fun get_equiv_rel ctxt s =
  (case Quotient_Info.lookup_quotients ctxt s of
    SOME {equiv_rel, ...} => equiv_rel
  | NONE => raise LIFT_MATCH ("get_equiv_rel (no quotient found for type " ^ s ^ ")"))

fun equiv_match_err ctxt ty_pat ty =
  let
    val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
    val ty_str = Syntax.string_of_typ ctxt ty
  in
    raise LIFT_MATCH (space_implode " "
      ["equiv_relation (Types ", quote ty_pat_str, "and", quote ty_str, " do not match.)"])
  end

(* builds the aggregate equivalence relation
   that will be the argument of Respects
*)
fun equiv_relation ctxt (rty, qty) =
  if rty = qty
  then HOLogic.eq_const rty
  else
    case (rty, qty) of
      (Type (s, tys), Type (s', tys')) =>
        if s = s'
        then
          let
            val args = map (equiv_relation ctxt) (tys ~~ tys')
          in
            list_comb (get_relmap ctxt s, args)
          end
        else
          let
            val (Type (_, rtys), qty_pat) = get_rty_qty ctxt s'
            val qtyenv = match ctxt equiv_match_err qty_pat qty
            val rtys' = map (Envir.subst_type qtyenv) rtys
            val args = map (equiv_relation ctxt) (tys ~~ rtys')
            val eqv_rel = get_equiv_rel ctxt s'
            val eqv_rel' = force_typ ctxt eqv_rel \<^Type>\<open>fun rty \<^Type>\<open>fun rty \<^Type>\<open>bool\<close>\<close>\<close>
          in
            if forall is_eq args
            then eqv_rel'
            else
              let
                val result = list_comb (get_relmap ctxt s, args)
              in
                mk_rel_compose (result, eqv_rel')
              end
          end
    | _ => HOLogic.eq_const rty


fun equiv_relation_chk ctxt (rty, qty) =
  equiv_relation ctxt (rty, qty)
  |> Syntax.check_term ctxt

(* generation of the Quotient theorem  *)

exception CODE_GEN of string

fun get_quot_thm ctxt s =
  (case Quotient_Info.lookup_quotients ctxt s of
    SOME {quot_thm, ...} => quot_thm
  | NONE => raise CODE_GEN ("No quotient type " ^ quote s ^ " found."));

fun get_rel_quot_thm ctxt s =
  (case Quotient_Info.lookup_quotmaps ctxt s of
    SOME {quot_thm, ...} => quot_thm
  | NONE => raise CODE_GEN ("get_relmap (no relation map function found for type " ^ s ^ ")"));

fun is_id_quot thm = Thm.eq_thm_prop (thm, @{thm identity_quotient3})

open Lifting_Util

infix 0 MRSL

exception NOT_IMPL of string

fun get_rel_from_quot_thm quot_thm = 
  let
    val (_ $ rel $ _ $ _) = (HOLogic.dest_Trueprop o Thm.prop_of) quot_thm
  in
    rel
  end

fun mk_quot_thm_compose (rel_quot_thm, quot_thm) = 
  let
    val quot_thm_rel = get_rel_from_quot_thm quot_thm
  in
    if is_eq quot_thm_rel then [rel_quot_thm, quot_thm] MRSL @{thm OOO_eq_quotient3}
    else raise NOT_IMPL "nested quotients: not implemented yet"
  end

fun prove_quot_thm ctxt (rty, qty) =
  if rty = qty
  then @{thm identity_quotient3}
  else
    case (rty, qty) of
      (Type (s, tys), Type (s', tys')) =>
        if s = s'
        then
          let
            val args = map (prove_quot_thm ctxt) (tys ~~ tys')
          in
            args MRSL (get_rel_quot_thm ctxt s)
          end
        else
          let
            val (Type (_, rtys), qty_pat) = get_rty_qty ctxt s'
            val qtyenv = match ctxt equiv_match_err qty_pat qty
            val rtys' = map (Envir.subst_type qtyenv) rtys
            val args = map (prove_quot_thm ctxt) (tys ~~ rtys')
            val quot_thm = get_quot_thm ctxt s'
          in
            if forall is_id_quot args
            then
              quot_thm
            else
              let
                val rel_quot_thm = args MRSL (get_rel_quot_thm ctxt s)
              in
                mk_quot_thm_compose (rel_quot_thm, quot_thm)
             end
          end
    | _ => @{thm identity_quotient3}



(*** Regularization ***)

(* Regularizing an rtrm means:

 - Quantifiers over types that need lifting are replaced
   by bounded quantifiers, for example:

      All P  ----> All (Respects R) P

   where the aggregate relation R is given by the rty and qty;

 - Abstractions over types that need lifting are replaced
   by bounded abstractions, for example:

      %x. P  ----> Ball (Respects R) %x. P

 - Equalities over types that need lifting are replaced by
   corresponding equivalence relations, for example:

      A = B  ----> R A B

   or

      A = B  ----> (R ===> R) A B

   for more complicated types of A and B


 The regularize_trm accepts raw theorems in which equalities
 and quantifiers match exactly the ones in the lifted theorem
 but also accepts partially regularized terms.

 This means that the raw theorems can have:
   Ball (Respects R),  Bex (Respects R), Bex1_rel (Respects R), Babs, R
 in the places where:
   All, Ex, Ex1, %, (op =)
 is required the lifted theorem.

*)

val mk_babs = Const (\<^const_name>\<open>Babs\<close>, dummyT)
val mk_ball = Const (\<^const_name>\<open>Ball\<close>, dummyT)
val mk_bex  = Const (\<^const_name>\<open>Bex\<close>, dummyT)
val mk_bex1_rel = Const (\<^const_name>\<open>Bex1_rel\<close>, dummyT)
val mk_resp = Const (\<^const_name>\<open>Respects\<close>, dummyT)

(* - applies f to the subterm of an abstraction,
     otherwise to the given term,
   - used by regularize, therefore abstracted
     variables do not have to be treated specially
*)
fun apply_subt f (trm1, trm2) =
  case (trm1, trm2) of
    (Abs (x, T, t), Abs (_ , _, t')) => Abs (x, T, f (t, t'))
  | _ => f (trm1, trm2)

fun term_mismatch str ctxt t1 t2 =
  let
    val t1_str = Syntax.string_of_term ctxt t1
    val t2_str = Syntax.string_of_term ctxt t2
    val t1_ty_str = Syntax.string_of_typ ctxt (fastype_of t1)
    val t2_ty_str = Syntax.string_of_typ ctxt (fastype_of t2)
  in
    raise LIFT_MATCH (cat_lines [str, t1_str ^ "::" ^ t1_ty_str, t2_str ^ "::" ^ t2_ty_str])
  end

(* the major type of All and Ex quantifiers *)
fun qnt_typ ty = domain_type (domain_type ty)

(* Checks that two types match, for example:
     rty -> rty   matches   qty -> qty *)
fun matches_typ ctxt rT qT =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    if rT = qT then true
    else
      (case (rT, qT) of
        (Type (rs, rtys), Type (qs, qtys)) =>
          if rs = qs then
            if length rtys <> length qtys then false
            else forall (fn x => x = true) (map2 (matches_typ ctxt) rtys qtys)
          else
            (case Quotient_Info.lookup_quotients_global thy qs of
              SOME {rtyp, ...} => Sign.typ_instance thy (rT, rtyp)
            | NONE => false)
      | _ => false)
  end


(* produces a regularized version of rtrm

   - the result might contain dummyTs

   - for regularization we do not need any
     special treatment of bound variables
*)
fun regularize_trm ctxt (rtrm, qtrm) =
  (case (rtrm, qtrm) of
    (Abs (x, ty, t), Abs (_, ty', t')) =>
      let
        val subtrm = Abs(x, ty, regularize_trm ctxt (t, t'))
      in
        if ty = ty' then subtrm
        else mk_babs $ (mk_resp $ equiv_relation ctxt (ty, ty')) $ subtrm
      end

  | (Const (\<^const_name>\<open>Babs\<close>, T) $ resrel $ (t as (Abs (_, ty, _))), t' as (Abs (_, ty', _))) =>
      let
        val subtrm = regularize_trm ctxt (t, t')
        val needres = mk_resp $ equiv_relation_chk ctxt (ty, ty')
      in
        if resrel <> needres
        then term_mismatch "regularize (Babs)" ctxt resrel needres
        else mk_babs $ resrel $ subtrm
      end

  | (Const (\<^const_name>\<open>All\<close>, ty) $ t, Const (\<^const_name>\<open>All\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
      in
        if ty = ty' then Const (\<^const_name>\<open>All\<close>, ty) $ subtrm
        else mk_ball $ (mk_resp $ equiv_relation ctxt (qnt_typ ty, qnt_typ ty')) $ subtrm
      end

  | (Const (\<^const_name>\<open>Ex\<close>, ty) $ t, Const (\<^const_name>\<open>Ex\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
      in
        if ty = ty' then Const (\<^const_name>\<open>Ex\<close>, ty) $ subtrm
        else mk_bex $ (mk_resp $ equiv_relation ctxt (qnt_typ ty, qnt_typ ty')) $ subtrm
      end

  | (Const (\<^const_name>\<open>Ex1\<close>, ty) $ (Abs (_, _,
      (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ (Const (\<^const_name>\<open>Set.member\<close>, _) $ _ $
        (Const (\<^const_name>\<open>Respects\<close>, _) $ resrel)) $ (t $ _)))),
     Const (\<^const_name>\<open>Ex1\<close>, ty') $ t') =>
      let
        val t_ = incr_boundvars (~1) t
        val subtrm = apply_subt (regularize_trm ctxt) (t_, t')
        val needrel = equiv_relation_chk ctxt (qnt_typ ty, qnt_typ ty')
      in
        if resrel <> needrel
        then term_mismatch "regularize (Bex1)" ctxt resrel needrel
        else mk_bex1_rel $ resrel $ subtrm
      end

  | (Const (\<^const_name>\<open>Ex1\<close>, ty) $ t, Const (\<^const_name>\<open>Ex1\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
      in
        if ty = ty' then Const (\<^const_name>\<open>Ex1\<close>, ty) $ subtrm
        else mk_bex1_rel $ (equiv_relation ctxt (qnt_typ ty, qnt_typ ty')) $ subtrm
      end

  | (Const (\<^const_name>\<open>Ball\<close>, ty) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ resrel) $ t,
     Const (\<^const_name>\<open>All\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
        val needrel = equiv_relation_chk ctxt (qnt_typ ty, qnt_typ ty')
      in
        if resrel <> needrel
        then term_mismatch "regularize (Ball)" ctxt resrel needrel
        else mk_ball $ (mk_resp $ resrel) $ subtrm
      end

  | (Const (\<^const_name>\<open>Bex\<close>, ty) $ (Const (\<^const_name>\<open>Respects\<close>, _) $ resrel) $ t,
     Const (\<^const_name>\<open>Ex\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
        val needrel = equiv_relation_chk ctxt (qnt_typ ty, qnt_typ ty')
      in
        if resrel <> needrel
        then term_mismatch "regularize (Bex)" ctxt resrel needrel
        else mk_bex $ (mk_resp $ resrel) $ subtrm
      end

  | (Const (\<^const_name>\<open>Bex1_rel\<close>, ty) $ resrel $ t, Const (\<^const_name>\<open>Ex1\<close>, ty') $ t') =>
      let
        val subtrm = apply_subt (regularize_trm ctxt) (t, t')
        val needrel = equiv_relation_chk ctxt (qnt_typ ty, qnt_typ ty')
      in
        if resrel <> needrel
        then term_mismatch "regularize (Bex1_res)" ctxt resrel needrel
        else mk_bex1_rel $ resrel $ subtrm
      end

  | (* equalities need to be replaced by appropriate equivalence relations *)
    (Const (\<^const_name>\<open>HOL.eq\<close>, ty), Const (\<^const_name>\<open>HOL.eq\<close>, ty')) =>
        if ty = ty' then rtrm
        else equiv_relation ctxt (domain_type ty, domain_type ty')

  | (* in this case we just check whether the given equivalence relation is correct *)
    (rel, Const (\<^const_name>\<open>HOL.eq\<close>, ty')) =>
      let
        val rel_ty = fastype_of rel
        val rel' = equiv_relation_chk ctxt (domain_type rel_ty, domain_type ty')
      in
        if rel' aconv rel then rtrm
        else term_mismatch "regularize (relation mismatch)" ctxt rel rel'
      end

  | (_, Const _) =>
      let
        val thy = Proof_Context.theory_of ctxt
        fun same_const t u =
          eq_Const_name (t, u) andalso matches_typ ctxt (dest_Const_type t) (dest_Const_type u)
      in
        if same_const rtrm qtrm then rtrm
        else
          let
            val rtrm' =
              (case Quotient_Info.lookup_quotconsts_global thy qtrm of
                SOME {rconst, ...} => rconst
              | NONE => term_mismatch "regularize (constant not found)" ctxt rtrm qtrm)
          in
            if Pattern.matches thy (rtrm', rtrm)
            then rtrm else term_mismatch "regularize (constant mismatch)" ctxt rtrm qtrm
          end
      end

  | (((t1 as Const (\<^const_name>\<open>case_prod\<close>, _)) $ Abs (v1, ty, Abs(v1', ty', s1))),
     ((t2 as Const (\<^const_name>\<open>case_prod\<close>, _)) $ Abs (v2, _ , Abs(v2', _  , s2)))) =>
       regularize_trm ctxt (t1, t2) $ Abs (v1, ty, Abs (v1', ty', regularize_trm ctxt (s1, s2)))

  | (((t1 as Const (\<^const_name>\<open>case_prod\<close>, _)) $ Abs (v1, ty, s1)),
     ((t2 as Const (\<^const_name>\<open>case_prod\<close>, _)) $ Abs (v2, _ , s2))) =>
       regularize_trm ctxt (t1, t2) $ Abs (v1, ty, regularize_trm ctxt (s1, s2))

  | (t1 $ t2, t1' $ t2') =>
       regularize_trm ctxt (t1, t1') $ regularize_trm ctxt (t2, t2')

  | (Bound i, Bound i') =>
      if i = i' then rtrm
      else raise (LIFT_MATCH "regularize (bounds mismatch)")

  | _ =>
      let
        val rtrm_str = Syntax.string_of_term ctxt rtrm
        val qtrm_str = Syntax.string_of_term ctxt qtrm
      in
        raise (LIFT_MATCH ("regularize failed (default: " ^ rtrm_str ^ "," ^ qtrm_str ^ ")"))
      end)

fun regularize_trm_chk ctxt (rtrm, qtrm) =
  regularize_trm ctxt (rtrm, qtrm)
  |> Syntax.check_term ctxt



(*** Rep/Abs Injection ***)

(*
Injection of Rep/Abs means:

  For abstractions:

  * If the type of the abstraction needs lifting, then we add Rep/Abs
    around the abstraction; otherwise we leave it unchanged.

  For applications:

  * If the application involves a bounded quantifier, we recurse on
    the second argument. If the application is a bounded abstraction,
    we always put an Rep/Abs around it (since bounded abstractions
    are assumed to always need lifting). Otherwise we recurse on both
    arguments.

  For constants:

  * If the constant is (op =), we leave it always unchanged.
    Otherwise the type of the constant needs lifting, we put
    and Rep/Abs around it.

  For free variables:

  * We put a Rep/Abs around it if the type needs lifting.

  Vars case cannot occur.
*)

fun mk_repabs ctxt (T, T') trm =
  absrep_fun ctxt RepF (T, T') $ (absrep_fun ctxt AbsF (T, T') $ trm)

fun inj_repabs_err ctxt msg rtrm qtrm =
  let
    val rtrm_str = Syntax.string_of_term ctxt rtrm
    val qtrm_str = Syntax.string_of_term ctxt qtrm
  in
    raise LIFT_MATCH (space_implode " " [msg, quote rtrm_str, "and", quote qtrm_str])
  end


(* bound variables need to be treated properly,
   as the type of subterms needs to be calculated   *)
fun inj_repabs_trm ctxt (rtrm, qtrm) =
 case (rtrm, qtrm) of
    (Const (\<^const_name>\<open>Ball\<close>, T) $ r $ t, Const (\<^const_name>\<open>All\<close>, _) $ t') =>
       Const (\<^const_name>\<open>Ball\<close>, T) $ r $ (inj_repabs_trm ctxt (t, t'))

  | (Const (\<^const_name>\<open>Bex\<close>, T) $ r $ t, Const (\<^const_name>\<open>Ex\<close>, _) $ t') =>
       Const (\<^const_name>\<open>Bex\<close>, T) $ r $ (inj_repabs_trm ctxt (t, t'))

  | (Const (\<^const_name>\<open>Babs\<close>, T) $ r $ t, t' as (Abs _)) =>
      let
        val rty = fastype_of rtrm
        val qty = fastype_of qtrm
      in
        mk_repabs ctxt (rty, qty) (Const (\<^const_name>\<open>Babs\<close>, T) $ r $ (inj_repabs_trm ctxt (t, t')))
      end

  | (t as Abs _, t' as Abs _) =>
      let
        val rty = fastype_of rtrm
        val qty = fastype_of qtrm
        val ((y, T), s) = Term.dest_abs_global t
        val (_, s') = Term.dest_abs_global t'
        val yvar = Free (y, T)
        val result = Term.lambda_name (y, yvar) (inj_repabs_trm ctxt (s, s'))
      in
        if rty = qty then result
        else mk_repabs ctxt (rty, qty) result
      end

  | (t $ s, t' $ s') =>
       (inj_repabs_trm ctxt (t, t')) $ (inj_repabs_trm ctxt (s, s'))

  | (Free (_, T), Free (_, T')) =>
        if T = T' then rtrm
        else mk_repabs ctxt (T, T') rtrm

  | (_, Const (\<^const_name>\<open>HOL.eq\<close>, _)) => rtrm

  | (_, Const (_, T')) =>
      let
        val rty = fastype_of rtrm
      in
        if rty = T' then rtrm
        else mk_repabs ctxt (rty, T') rtrm
      end

  | _ => inj_repabs_err ctxt "injection (default):" rtrm qtrm

fun inj_repabs_trm_chk ctxt (rtrm, qtrm) =
  inj_repabs_trm ctxt (rtrm, qtrm)
  |> Syntax.check_term ctxt



(*** Wrapper for automatically transforming an rthm into a qthm ***)

(* substitutions functions for r/q-types and
   r/q-constants, respectively
*)
fun subst_typ ctxt ty_subst rty =
  case rty of
    Type (s, rtys) =>
      let
        val thy = Proof_Context.theory_of ctxt
        val rty' = Type (s, map (subst_typ ctxt ty_subst) rtys)

        fun matches [] = rty'
          | matches ((rty, qty)::tail) =
              (case try (Sign.typ_match thy (rty, rty')) Vartab.empty of
                NONE => matches tail
              | SOME inst => subst_typ ctxt ty_subst (Envir.subst_type inst qty))
      in
        matches ty_subst
      end
  | _ => rty

fun subst_trm ctxt ty_subst trm_subst rtrm =
  case rtrm of
    t1 $ t2 => (subst_trm ctxt ty_subst trm_subst t1) $ (subst_trm ctxt ty_subst trm_subst t2)
  | Abs (x, ty, t) => Abs (x, subst_typ ctxt ty_subst ty, subst_trm ctxt ty_subst trm_subst t)
  | Free(n, ty) => Free(n, subst_typ ctxt ty_subst ty)
  | Var(n, ty) => Var(n, subst_typ ctxt ty_subst ty)
  | Bound i => Bound i
  | Const (a, ty) =>
      let
        val thy = Proof_Context.theory_of ctxt

        fun matches [] = Const (a, subst_typ ctxt ty_subst ty)
          | matches ((rconst, qconst)::tail) =
              (case try (Pattern.match thy (rconst, rtrm)) (Vartab.empty, Vartab.empty) of
                NONE => matches tail
              | SOME inst => subst_trm ctxt ty_subst trm_subst (Envir.subst_term inst qconst))
      in
        matches trm_subst
      end

(* generate type and term substitutions out of the
   qtypes involved in a quotient; the direction flag
   indicates in which direction the substitutions work:

     true:  quotient -> raw
     false: raw -> quotient
*)
fun mk_ty_subst qtys direction ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Quotient_Info.dest_quotients ctxt
    |> map (fn x => (#rtyp x, #qtyp x))
    |> filter (fn (_, qty) => member (Sign.typ_instance thy o swap) qtys qty)
    |> map (if direction then swap else I)
  end

fun mk_trm_subst qtys direction ctxt =
  let
    val subst_typ' = subst_typ ctxt (mk_ty_subst qtys direction ctxt)
    fun proper (t1, t2) = subst_typ' (fastype_of t1) = fastype_of t2

    val const_substs =
      Quotient_Info.dest_quotconsts ctxt
      |> map (fn x => (#rconst x, #qconst x))
      |> map (if direction then swap else I)

    val rel_substs =
      Quotient_Info.dest_quotients ctxt
      |> map (fn x => (#equiv_rel x, HOLogic.eq_const (#qtyp x)))
      |> map (if direction then swap else I)
  in
    filter proper (const_substs @ rel_substs)
  end


(* derives a qtyp and qtrm out of a rtyp and rtrm,
   respectively
*)
fun derive_qtyp ctxt qtys rty =
  subst_typ ctxt (mk_ty_subst qtys false ctxt) rty

fun derive_qtrm ctxt qtys rtrm =
  subst_trm ctxt (mk_ty_subst qtys false ctxt) (mk_trm_subst qtys false ctxt) rtrm

(* derives a rtyp and rtrm out of a qtyp and qtrm,
   respectively
*)
fun derive_rtyp ctxt qtys qty =
  subst_typ ctxt (mk_ty_subst qtys true ctxt) qty

fun derive_rtrm ctxt qtys qtrm =
  subst_trm ctxt (mk_ty_subst qtys true ctxt) (mk_trm_subst qtys true ctxt) qtrm

end;
