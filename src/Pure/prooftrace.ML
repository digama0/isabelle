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
  val assume_proof: term -> sort list -> T
  val implies_intr_proof: term -> sort list -> T -> T
  val implies_elim_proof: T -> T -> T
  val forall_intr_proof: term -> sort list -> T -> T
  val forall_elim_proof: T -> term -> sort list -> T
  val reflexive_proof: term -> sort list -> T
  val symmetric_proof: T -> T
  val transitive_proof: T -> T -> T
  val beta_proof: bool -> term -> sort list -> T
  val eta_proof: term -> sort list -> T
  val eta_long_proof: term -> sort list -> T
  val abstract_rule_proof: term -> T -> T
  val combination_proof: T -> T -> T
  val equal_intr_proof: T -> T -> T
  val equal_elim_proof: T -> T -> T
  val flexflex_proof: Envir.env -> T -> T
  val generalize_proof: Names.set * Names.set -> int -> T -> T
  val instantiate_proof:
    ((indexname * sort) * typ) list * ((indexname * typ) * term) list -> sort list -> T -> T
  val trivial_proof: sort list -> T
  val of_class_proof: typ * class -> T
  val thm_proof: serial -> T
  val constrain_thm_proof: serial -> sort list -> term list -> term -> T
  val varifyT_proof: ((string * sort) * (indexname * sort)) list -> T -> T
  val legacy_freezeT_proof: T -> T
  val lift_proof: term -> int -> sort list -> T -> T
  val assumption_proof: int -> int -> T -> T
  val eq_assumption_proof: int -> T -> T
  val rotate_proof: int -> int -> T -> T
  val permute_prems_proof: int -> int -> T -> T
  val bicompose_proof: Envir.env -> (term * term) list -> int -> bool -> term list ->
    term option -> int -> int -> int -> T -> T -> T

  val export_proof: theory -> thm_header -> (typ * typ) list -> int -> term list -> T -> unit
  val log: string -> unit
  val props_enabled: unit -> bool
  val prop_proof: term -> sort list -> (term * term) list -> T -> T
  val log_stats: unit -> unit
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
  | PTHyp of term * sort list
  | PTImpIntr of term * sort list * T
  | PTImpElim of T * T
  | PTForallIntr of term * sort list * T
  | PTForallElim of term * sort list * T
  | PTAxiom of string * term * Theory.axiom_source
  | PTOracle of string * term
  | PTRefl of term * sort list
  | PTSymm of T
  | PTTrans of T * T
  | PTBetaNorm of term * sort list
  | PTBetaHead of term * sort list
  | PTEta of term * sort list
  | PTEtaLong of term * sort list
  | PTStripSHyps of sort list * T
  | PTAbsRule of term * T
  | PTAppRule of T * T
  | PTEqIntr of T * T
  | PTEqElim of T * T
  | PTFlexFlex of Envir.env * T
  | PTGeneralize of Names.set * Names.set * int * T
  | PTInstantiate of ((indexname * sort) * typ) list * ((indexname * typ) * term) list *
      sort list * T
  | PTTrivial of sort list
  | PTOfClass of typ * class
  | PTThm of serial
  | PTConstrainThm of serial * sort list * term list * term
  | PTVarify of ((string * sort) * (indexname * sort)) list * T
  | PTLegacyFreezeT of T
  | PTLift of term * int * sort list * T
  | PTIncrIndexes of int * T
  | PTAssumption of int * int * T
  | PTEqAssumption of int * T
  | PTRotate of int * int * T
  | PTPermutePrems of int * int * T
  | PTBicompose of (Envir.env * (term * term) list * int * bool * term list *
    term option * int * int * int) * T * T
  | PTPruned
  (*debug aid: what this subproof proves -- statement, sort hypotheses and flex-flex
    pairs.  Named to sort last so that the constructor tags of everything above are
    unchanged.*)
  | PTZProp of term * sort list * (term * term) list * T;

val sorry = PTSorry;
val pruned = PTPruned;
fun axiom_proof name prop src = PTAxiom (name, prop, src);
fun oracle_proof name prop = PTOracle (name, prop);
fun implies_intr_proof A sorts p = PTImpIntr (A, sorts, p);
fun implies_elim_proof p q = PTImpElim (p, q);
fun forall_intr_proof x sorts p = PTForallIntr (x, sorts, p);
fun forall_elim_proof p t sorts = PTForallElim (t, sorts, p);
fun assume_proof t sorts = PTHyp (t, sorts);
fun reflexive_proof t sorts = PTRefl (t, sorts);
val symmetric_proof = PTSymm;
fun transitive_proof p q = PTTrans (p, q);
fun strip_shyps_proof sorts p = PTStripSHyps (sorts, p);
fun beta_proof true t sorts = PTBetaNorm (t, sorts)
  | beta_proof false t sorts = PTBetaHead (t, sorts);
fun eta_proof t sorts = PTEta (t, sorts);
fun eta_long_proof t sorts = PTEtaLong (t, sorts);
fun abstract_rule_proof x p = PTAbsRule (x, p);
fun combination_proof p q = PTAppRule (p, q);
fun equal_intr_proof p q = PTEqIntr (p, q);
fun equal_elim_proof p q = PTEqElim (p, q);
fun flexflex_proof env p = PTFlexFlex (env, p);
fun generalize_proof (tfrees, frees) idx p = PTGeneralize (tfrees, frees, idx, p);
fun instantiate_proof (instT, inst) sorts p = PTInstantiate (instT, inst, sorts, p);
fun trivial_proof sorts = PTTrivial sorts;
val of_class_proof = PTOfClass;
val thm_proof = PTThm;
fun constrain_thm_proof i shyps hyps prop = PTConstrainThm (i, shyps, hyps, prop);
fun varifyT_proof al p = PTVarify (al, p);
val legacy_freezeT_proof = PTLegacyFreezeT;
fun lift_proof gprop inc sorts p = PTLift (gprop, inc, sorts, p);
fun incr_indexes_proof i p = PTIncrIndexes (i, p);
fun assumption_proof i n p = PTAssumption (i, n, p);
fun eq_assumption_proof i p = PTEqAssumption (i, p);
fun rotate_proof k i p = PTRotate (k, i, p);
fun permute_prems_proof j k p = PTPermutePrems (j, k, p);
fun bicompose_proof env tpairs nsubgoal flatten As A n nlift nbs p q =
  PTBicompose ((env, tpairs, nsubgoal, flatten, As, A, n, nlift, nbs), p, q);

fun enabled () = Options.default_bool "prooftrace_enabled";
fun props_enabled () = Options.default_bool "prooftrace_props";
fun prop_proof prop shyps tpairs p = PTZProp (prop, shyps, tpairs, p);
fun when f = if enabled () then f () else PTSorry;

fun logging () = Options.default_bool "prooftrace_log";

fun log s =
  if logging () then File.append (Path.explode "$ISABELLE_HOME_USER/prooftrace.log") (s ^ "\n")
  else ();

fun write_all fd bytes =
  let
    val n = Word8Vector.length bytes
    fun loop i =
      if i >= n then ()
      else loop (i + Posix.IO.writeVec (fd, Word8VectorSlice.slice (bytes, i, NONE)))
  in loop 0 end;

(*inline: Socket_IO is loaded after this file in ROOT.ML, and open_streams would hide the
  file descriptor behind BinPrimIO closures anyway*)
fun open_socket_inet name =
  (case String.tokens (fn c => c = #":") name of
    [h, p] =>
      (case (NetHostDB.getByName h, Int.fromString p) of
        (SOME host, SOME port) =>
          let val socket: Socket.active INetSock.stream_sock = INetSock.TCP.socket ()
          in
            (*a blocked write() holds ML memory and so freezes GC for the whole prover:
              give the kernel room to absorb a whole trace without us waiting*)
            Socket.Ctl.setSNDBUF (socket, 4 * 1024 * 1024) handle OS.SysErr _ => ();
            Socket.connect (socket, INetSock.toAddr (NetHostDB.addr host, port));
            socket
          end
      | _ => error ("prooftrace: bad socket address " ^ name))
  | _ => error ("prooftrace: bad socket address " ^ name));

(*where does the prover actually block?  (count, unused, writing)*)
val stats = Synchronized.var "prooftrace_stats" (0, Time.zeroTime, Time.zeroTime);

fun add_stat wait write =
  Synchronized.change stats (fn (n, w, x) => (n + 1, w + wait, x + write));

(*independent of prooftrace_log: one line per theory, so a benchmark run can report where
  the prover blocked without paying for per-trace logging*)
fun log_stats () =
  let val (n, _, x) = Synchronized.value stats in
    if n = 0 then () else
      File.append (Path.explode "$ISABELLE_HOME_USER/prooftrace_stats.log")
        ("prooftrace ML: " ^ string_of_int n ^ " exports, write " ^ Time.message x ^ "\n")
  end;

fun export_to_socket addr thy_name serial data =
  let
    val write_start = Timing.start ()
    val socket = open_socket_inet addr
    val fd =
      (case Posix.FileSys.iodToFD (Socket.ioDesc socket) of
        SOME fd => fd
      | NONE => raise Fail "prooftrace: socket has no file descriptor")
    val () = write_all fd (Byte.stringToBytes (thy_name ^ "\n" ^ string_of_int serial ^ "\n"))
    val () = PolyML.exportSmallToFD (fd, data)
      handle e => (Socket.close socket; Exn.reraise e)
  in
    Socket.close socket;
    add_stat Time.zeroTime (#elapsed (Timing.result write_start))
  end;

fun export_proof thy header tvar_map shyps hyps p =
  if not (Options.default_bool "prooftrace_out") then () else
  let
    val logit = logging ();
    val () = if logit then
      log ("trace " ^ string_of_int (#serial header) ^ ": start " ^
        the_default "" (Position.file_of (#command_pos header)) ^ ":" ^
        string_of_int (the_default 0 (Position.line_of (#command_pos header))))
      else ();
    val start = Timing.start ();

    val data = (header, tvar_map, shyps, hyps, p)
    val addr = Options.default_string "prooftrace_socket"
    val size_hint =
      if addr <> "" then
        (*v11: stream the image straight to a fresh socket to the Scala build job.  No
          in-memory image, no YXML escaping, no protocol copy; the close frames the
          message, which matters because the length is unknown until it is written.*)
        (export_to_socket addr (Context.theory_base_name thy) (#serial header) data; 0)
      else
        let val s = YXML.escape (Byte.bytesToString (PolyML.exportSmall data)) in
          Export.export thy
            (Path.binding0 (Path.make ["proof_trace", string_of_int (#serial header)]))
            [XML.Text s];
          size s
        end

    val () = if logit then
      let val {elapsed, ...} = Timing.result start in
        log ("trace " ^ string_of_int (#serial header) ^
          "(" ^ string_of_int size_hint ^ " bytes, " ^ Time.message elapsed ^ "): " ^
            (Print_Mode.with_modes [""]
              (fn () => Syntax.string_of_term (Syntax.init_pretty_global thy) (#prop header)) ()
              handle Fail _ => "..."))
      end
      else ()
  in () end;

end;
