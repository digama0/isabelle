(*  Title:      Pure/prooftrace.ML
    Author:     Mario Carneiro

Tight representation of types / terms / proof terms, notably for proof recording.
*)

(*** global ***)

(*** local ***)

signature PROOFTRACE =
sig
  type T

  type thm_header =
    {serial: serial, command_pos: Position.T, theory_name: string, thm_name: Thm_Name.P,
      prop: term, types: typ list option};

  val sorry: T
  val pruned: T

  val enabled: unit -> bool
  val when: (unit -> T) -> T

  val axiom_proof: string -> term -> T
  val oracle_proof:  string -> term -> T
  val strip_shyps_proof: T -> T
  val incr_indexes_proof: int -> T -> T
  val assume_proof: term -> T
  val implies_intr_proof: term -> T -> T
  val implies_elim_proof: T -> T -> T
  val forall_intr_proof: term -> T -> T
  val forall_elim_proof: T -> term -> T
  val reflexive_proof: term -> T
  val symmetric_proof: T -> T
  val transitive_proof: T -> T -> T
  val beta_proof: bool -> term -> T
  val eta_proof: term -> T
  val eta_long_proof: term -> T
  val abstract_rule_proof: term -> T -> T
  val combination_proof: T -> T -> T
  val equal_intr_proof: T -> T -> T
  val equal_elim_proof: T -> T -> T
  val flexflex_proof: Envir.env -> T -> T
  val generalize_proof: Names.set * Names.set -> int -> T -> T
  val instantiate_proof:
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list -> T -> T
  val trivial_proof: T
  val of_class_proof: typ * class -> T
  val thm_proof: serial -> T
  val constrain_thm_proof: serial -> sort list -> term list -> term -> T
  val varifyT_proof: ((string * sort) * (indexname * sort)) list -> T -> T
  val legacy_freezeT_proof: T -> T
  val lift_proof: term -> int -> T -> T
  val assumption_proof: int -> int -> T -> T
  val eq_assumption_proof: int -> T -> T
  val rotate_proof: int -> int -> T -> T
  val permute_prems_proof: int -> int -> T -> T
  val bicompose_proof: Envir.env -> int -> bool -> term list -> term list ->
    term option -> term list -> int -> int -> T -> T -> T

  val export_proof: theory -> thm_header -> (typ * typ) list -> int -> term list -> T -> unit
end;

structure Prooftrace: PROOFTRACE =
struct

type thm_header =
  {serial: serial, command_pos: Position.T, theory_name: string, thm_name: Thm_Name.P,
    prop: term, types: typ list option};

datatype T =
    PTSorry
  | PTHyp of term
  | PTImpIntr of term * T
  | PTImpElim of T * T
  | PTForallIntr of term * T
  | PTForallElim of T * term
  | PTAxiom of string * term
  | PTOracle of string * term
  | PTRefl of term
  | PTSymm of T
  | PTTrans of T * T
  | PTBetaNorm of term
  | PTBetaHead of term
  | PTEta of term
  | PTEtaLong of term
  | PTStripSHyps of T
  | PTAbsRule of term * T
  | PTAppRule of T * T
  | PTEqIntr of T * T
  | PTEqElim of T * T
  | PTFlexFlex of Envir.env * T
  | PTGeneralize of Names.set * Names.set * int * T
  | PTInstantiate of ((indexname * sort) * typ) list * ((indexname * typ) * term) list * T
  | PTTrivial
  | PTOfClass of typ * class
  | PTThm of serial
  | PTConstrainThm of serial * sort list * term list * term
  | PTVarify of ((string * sort) * (indexname * sort)) list * T
  | PTLegacyFreezeT of T
  | PTLift of term * int * T
  | PTIncrIndexes of int * T
  | PTAssumption of (T * int) * int
  | PTEqAssumption of T * int
  | PTRotate of int * int * T
  | PTPermutePrems of int * int * T
  | PTBicompose of Envir.env * int * bool * term list * term list *
    term option * term list * int * int * T * T
  | PTPruned;

val sorry = PTSorry;
val pruned = PTPruned;
fun axiom_proof name prop = PTAxiom (name, prop);
fun oracle_proof name prop = PTOracle (name, prop);
fun implies_intr_proof A p = PTImpIntr (A, p);
fun implies_elim_proof p q = PTImpElim (p, q);
fun forall_intr_proof x p = PTForallIntr (x, p);
fun forall_elim_proof p t = PTForallElim (p, t);
val assume_proof = PTHyp;
val reflexive_proof = PTRefl;
val symmetric_proof = PTSymm;
fun transitive_proof p q = PTTrans (p, q);
val strip_shyps_proof = PTStripSHyps;
fun beta_proof true = PTBetaNorm
  | beta_proof false = PTBetaHead;
val eta_proof = PTEta;
val eta_long_proof = PTEtaLong;
fun abstract_rule_proof x p = PTAbsRule (x, p);
fun combination_proof p q = PTAppRule (p, q);
fun equal_intr_proof p q = PTEqIntr (p, q);
fun equal_elim_proof p q = PTEqElim (p, q);
fun flexflex_proof env p = PTFlexFlex (env, p);
fun generalize_proof (tfrees, frees) idx p = PTGeneralize (tfrees, frees, idx, p);
fun instantiate_proof (instT, inst) p = PTInstantiate (instT, inst, p);
val trivial_proof = PTTrivial;
val of_class_proof = PTOfClass;
val thm_proof = PTThm;
fun constrain_thm_proof i shyps hyps prop = PTConstrainThm (i, shyps, hyps, prop);
fun varifyT_proof al p = PTVarify (al, p);
val legacy_freezeT_proof = PTLegacyFreezeT;
fun lift_proof gprop inc p = PTLift (gprop, inc, p);
fun incr_indexes_proof i p = PTIncrIndexes (i, p);
fun assumption_proof i n p = PTAssumption ((p, i), n);
fun eq_assumption_proof i p = PTEqAssumption (p, i);
fun rotate_proof k i p = PTRotate (k, i, p);
fun permute_prems_proof j k p = PTPermutePrems (j, k, p);
fun bicompose_proof env smax flatten Bs As A oldAs n nlift p q =
  PTBicompose (env, smax, flatten, Bs, As, A, oldAs, n, nlift, p, q);

val proofs = Unsynchronized.ref true;
fun enabled () = ! proofs;
fun when f = if enabled () then f () else PTSorry;

exception OutOfRange;

fun EVariant (i, ls) = XML.Elem ((i, []), ls)
fun EList ls = XML.Elem ((":", []), ls)
fun ETuple ls = XML.Elem ((":", []), ls)
fun EInt i = XML.Text (string_of_int i)
fun EString s = XML.Text s;

fun tree_ord (XML.Elem a1, XML.Elem a2) =
      prod_ord (fn (a, b) => fast_string_ord (#1 a, #1 b)) (list_ord tree_ord) (a1, a2)
  | tree_ord (XML.Text a1, XML.Text a2) = fast_string_ord (a1, a2)
  | tree_ord (XML.Elem _, XML.Text _) = LESS
  | tree_ord (XML.Text _, XML.Elem _) = GREATER;

structure ElemTab = Table(type key = XML.tree val ord = tree_ord);

fun export_proof thy header tvar_map shyps hyps p =
  let
    fun mk_tab encode =
      let val tab = Unsynchronized.ref (ElemTab.empty, [])
      in
        (fn () => let val (_, b) = !tab in b end, fn p =>
        let val (tab1, vec1) = !tab; val p = encode p in
          case ElemTab.lookup tab1 p of
            SOME i => EInt i
          | NONE =>
            let val i = ElemTab.size tab1
            in tab := (ElemTab.update_new (p, i) tab1, p :: vec1); EInt i end
        end)
      end;

    fun opt f a = EList (case a of NONE => [] | SOME a => [f a])

    val (strings, hash_string) = mk_tab EString
    val hash_class = hash_string
    val (sorts, hash_sort) = mk_tab (EList o map hash_class)
    val (indexnames, hash_indexname) = mk_tab (fn (s, i) => ETuple [hash_string s, EInt i])
    val (names, hash_names) = mk_tab (fn s => EList (map (fn (s, i) =>
      ETuple [hash_string s, EInt i]) (Names.dest s)))

    val (typs, hash_typ') = mk_tab I
    fun hash_typ t = hash_typ' (case t of
        Type(s, tys) => EVariant("T", [hash_string s, EList (map hash_typ tys)])
      | TFree(x, s) => EVariant("F", [hash_string x, hash_sort s])
      | TVar(i, s) => EVariant("V", [hash_indexname i, hash_sort s]))

    val (terms, hash_term') = mk_tab I
    fun hash_term t = hash_term' (case t of
        Const(c, ty) => EVariant("C", [hash_string c, hash_typ ty])
      | Free(x, ty) => EVariant("F", [hash_string x, hash_typ ty])
      | Var(x, ty) => EVariant("V", [hash_indexname x, hash_typ ty])
      | Bound(i) => EVariant("B", [EInt i])
      | Abs(x, ty, e) => EVariant("L", [hash_string x, hash_typ ty, hash_term e])
      | e1 $ e2 => EVariant("A", [hash_term e1, hash_term e2]))

    fun enc_env (Envir.Envir {maxidx, tenv, tyenv}) =
      ETuple [EInt maxidx,
        EList (map (fn ((a, b), (c, d)) =>
          ETuple [hash_string a, EInt b, hash_typ c, hash_term d]) (Vartab.dest tenv)),
        EList (map (fn ((a, b), (c, d)) =>
          ETuple [hash_string a, EInt b, hash_sort c, hash_typ d]) (Vartab.dest tyenv))]

    val (proofs, hash_proof') = mk_tab I
    val (assumptions, hash_assumption') = mk_tab I
    fun hash_assumption (s, i) = hash_assumption' (ETuple [hash_proof s, EInt i])
    and hash_proof p = hash_proof' (case p of
        PTSorry => EVariant("?", [])
      | PTHyp(a) => EVariant("X", [hash_term a])
      | PTImpIntr(a, p) => EVariant("i", [hash_term a, hash_proof p])
      | PTImpElim(p, q) => EVariant("I", [hash_proof p, hash_proof q])
      | PTForallIntr(a, p) => EVariant("f", [hash_term a, hash_proof p])
      | PTForallElim(p, a) => EVariant("F", [hash_proof p, hash_term a])
      | PTAxiom(a, b) => EVariant("A", [hash_string a, hash_term b])
      | PTOracle(a, b) => EVariant("O", [hash_string a, hash_term b])
      | PTRefl(a) => EVariant("=", [hash_term a])
      | PTSymm(p) => EVariant("-", [hash_proof p])
      | PTTrans(p, q) => EVariant("+", [hash_proof p, hash_proof q])
      | PTBetaNorm(a) => EVariant("B", [hash_term a])
      | PTBetaHead(a) => EVariant("b", [hash_term a])
      | PTEta(a) => EVariant("h", [hash_term a])
      | PTEtaLong(a) => EVariant("H", [hash_term a])
      | PTStripSHyps(p) => EVariant("p", [hash_proof p])
      | PTAbsRule(a, p) => EVariant("l", [hash_term a, hash_proof p])
      | PTAppRule(p, q) => EVariant("c", [hash_proof p, hash_proof q])
      | PTEqIntr(p, q) => EVariant("e", [hash_proof p, hash_proof q])
      | PTEqElim(p, q) => EVariant("E", [hash_proof p, hash_proof q])
      | PTFlexFlex(e, p) => EVariant("x", [enc_env e, hash_proof p])
      | PTGeneralize(a, b, c, p) => EVariant("G", [hash_names a, hash_names b, EInt c, hash_proof p])
      | PTInstantiate(a, b, p) => EVariant("N", [
          EList (map (fn ((a, b), c) => ETuple [hash_indexname a, hash_sort b, hash_typ c]) a),
          EList (map (fn ((a, b), c) => ETuple [hash_indexname a, hash_typ b, hash_term c]) b),
          hash_proof p])
      | PTTrivial => EVariant("t", [])
      | PTOfClass(a, b) => EVariant("o", [hash_typ a, hash_class b])
      | PTThm(i) => EVariant("T", [EInt i])
      | PTConstrainThm(i, sh, h, t) => EVariant("K", [
          EInt i, EList (map hash_sort sh), EList (map hash_term h), hash_term t])
      | PTVarify(a, p) => EVariant("V", [
          EList (map (fn ((a, b), (c, d)) =>
            ETuple [hash_string a, hash_sort b, hash_indexname c, hash_sort d]) a),
          hash_proof p])
      | PTLegacyFreezeT(p) => EVariant("g", [hash_proof p])
      | PTLift(a, b, p) => EVariant("L", [hash_term a, EInt b, hash_proof p])
      | PTIncrIndexes(a, p) => EVariant("k", [EInt a, hash_proof p])
      | PTAssumption(p, a) => EVariant("a", [hash_assumption p, EInt a])
      | PTEqAssumption p => EVariant("q", [hash_assumption p])
      | PTRotate(a, b, p) => EVariant("R", [EInt a, EInt b, hash_proof p])
      | PTPermutePrems(a, b, p) => EVariant("P", [EInt a, EInt b, hash_proof p])
      | PTBicompose(a, b, c, d, e, f, g, h, i, p, q) => EVariant("C", [
          enc_env a, EInt b, EInt (if c then 1 else 0),
          EList (map hash_term d), EList (map hash_term e), opt hash_term f,
          EList (map hash_term g), EInt h, EInt i, hash_proof p, hash_proof q])
      | PTPruned => EVariant("!", []))

    fun enc_position pos =
      let val {line, offset, end_offset, props = {label, file, id}} = Position.dest pos
      in ETuple [EInt line, EInt offset, EInt end_offset,
        hash_string label, hash_string file, hash_string id] end
    fun enc_thm_name ((name, i), pos) = ETuple [hash_string name, EInt i, enc_position pos]
    fun enc_header {serial, command_pos, theory_name, thm_name, prop, types} =
      ETuple [EInt serial, enc_position command_pos, hash_string theory_name,
        enc_thm_name thm_name, hash_term prop, opt (EList o map hash_typ) types]

    val enc_root = [enc_header header,
      EList (map (fn (a, b) => ETuple [hash_typ a, hash_typ b]) tvar_map),
      EInt shyps, EList (map hash_term hyps), hash_proof p]

    val s = map (fn f => EList (rev (f ())))
      [strings,sorts,indexnames,names,typs,terms,proofs,assumptions];
  in
    Export.export thy (Path.binding0 (Path.make ["exportTrace", string_of_int (#serial header)]))
      (s @ [ETuple enc_root])
  end;

end;
