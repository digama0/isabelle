(*  Title:      Pure/prooftrace.ML
    Author:     Mario Carneiro

Tight representation of types / terms / proof terms, notably for proof recording.
*)

(*** global ***)

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

  val axiom_proof: string -> term -> Theory.axiom_source -> T
  val oracle_proof:  string -> term -> T
  val strip_shyps_proof: sort list -> T -> T
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
  val bicompose_proof: Envir.env -> (term * term) list -> int -> bool -> term list ->
    term option -> int -> int -> T -> T -> T

  val export_proof: theory -> thm_header -> (typ * typ) list -> int -> term list -> T -> unit
end;

(*** local ***)

functor Prooftrace_Table(Key: KEY): sig
  val mk_tab_rec: (int -> 'b) -> (unit -> 'a list) * ((Key.key -> 'a) -> Key.key -> 'b)
  val mk_tab: (int -> 'b) -> (Key.key -> 'a) -> (unit -> 'a list) * (Key.key -> 'b)
end = struct
  structure Table = Table(Key);

  fun mk_tab_rec decode =
    let val tab = Unsynchronized.ref (Table.empty, [])
    in
      (fn () => let val (_, b) = !tab in b end, fn encode => fn p =>
        case Table.lookup (#1 (!tab)) p of
          SOME i => decode i
        | NONE =>
          let
            val p' = encode p
            val (tab1, vec1) = !tab
            val i = Table.size tab1
            val () = tab := (Table.update_new (p, i) tab1, p' :: vec1)
          in decode i end)
    end;

  fun mk_tab decode encode =
    let val (out, map) = mk_tab_rec decode in (out, map encode) end
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
  | PTAxiom of string * term * Theory.axiom_source
  | PTOracle of string * term
  | PTRefl of term
  | PTSymm of T
  | PTTrans of T * T
  | PTBetaNorm of term
  | PTBetaHead of term
  | PTEta of term
  | PTEtaLong of term
  | PTStripSHyps of sort list * T
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
  | PTBicompose of Envir.env * (term * term) list * int * bool * term list *
    term option * int * int * T * T
  | PTPruned;

val sorry = PTSorry;
val pruned = PTPruned;
fun axiom_proof name prop src = PTAxiom (name, prop, src);
fun oracle_proof name prop = PTOracle (name, prop);
fun implies_intr_proof A p = PTImpIntr (A, p);
fun implies_elim_proof p q = PTImpElim (p, q);
fun forall_intr_proof x p = PTForallIntr (x, p);
fun forall_elim_proof p t = PTForallElim (p, t);
val assume_proof = PTHyp;
val reflexive_proof = PTRefl;
val symmetric_proof = PTSymm;
fun transitive_proof p q = PTTrans (p, q);
fun strip_shyps_proof sorts p = PTStripSHyps (sorts, p);
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
fun bicompose_proof env tpairs nsubgoal flatten As A n nlift p q =
  PTBicompose (env, tpairs, nsubgoal, flatten, As, A, n, nlift, p, q);

fun enabled () = Options.default_bool "prooftrace_enabled";
fun when f = if enabled () then f () else PTSorry;

fun export_proof thy header tvar_map shyps hyps p =
  if not (Options.default_bool "prooftrace_out") then () else
  let
    val data = (header, tvar_map, shyps, hyps, p)
  in
    Export.export thy (Path.binding0 (Path.make ["proof_trace", string_of_int (#serial header)]))
      [XML.Text (Byte.bytesToString (PolyML.exportSmall data))]
  end;

end;
