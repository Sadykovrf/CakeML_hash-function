open preamble
open basis
open basisProgTheory
open ml_monad_translator_interfaceLib
open HashFunctionProgTheory
open HashFunctionFFITheory
open integerTheory
open cfDivTheory
open cfDivLib
open cfMonadTheory

val _ = new_theory "HashFunctionProof";

val _ = translation_extends"HashFunctionProg";

fun xcf' s = xcf_with_def ("HashFunction." ^ s) 
             (DB.fetch "HashFunctionProg" ("HashFunction_" ^ s ^ "_v_def"));

(* Avoid printing potentially very long output *)
(* val _ = Globals.max_print_depth := 10000; *)

(* val st = get_ml_prog_state(); *) 

val MONAD_HASH_IO_def = Define ` 
    MONAD_HASH_IO ev = IOx ev_ffi_part ev
 `;

Theorem MONAD_HASH_FFI_part_hprop:
  FFI_part_hprop (MONAD_HASH_IO x)
Proof
rw [MONAD_HASH_IO_def,cfHeapsBaseTheory.IO_def,cfMainTheory.FFI_part_hprop_def,
      cfHeapsBaseTheory.IOx_def, ev_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR ]
  \\ fs[set_sepTheory.one_def]
QED

Theorem explode_thm_1[simp]:
   !msg. ?s. ( (explode (msg) = s) /\ (msg = strlit s) )
Proof
  rw[]
  \\ ASSUME_TAC implode_explode
  \\ metis_tac[implode_def]
QED

val CFS_def =  Define `
    (CFS (message:mlstring) ) : word8 list = 
               if (strlen message)>=32 then TAKE 32 (MAP ((n2w : num -> word8) o ORD) (explode message)) 
                             else 
                   (MAP (n2w o ORD) (explode message))++(REPLICATE (32-(strlen message)) (0w: word8)) `;

Theorem hash_basic_spec:
  !messagev message ev.
  STRING_TYPE message messagev ==>
  app (p:'ffi ffi_proj) HashFunction_calculate_from_string_v [messagev]
    (MONAD_HASH_IO ev)
    (POSTv v. & LIST_TYPE WORD8 (CFS message) v *
               MONAD_HASH_IO ev)
Proof
rw []
  \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [MONAD_HASH_IO_def, ev_ffi_part_def, IOx_def, IO_def]
  \\ xpull
  \\ qunabbrev_tac `Q`
  \\ rpt (pop_assum mp_tac)
  \\ xcf' "calculate_from_string"
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xsimpl \\ xcon \\ xsimpl)
  \\ rpt (xlet_auto THEN1 xsimpl)
  \\ qmatch_goalsub_rename_tac `W8ARRAY result`
  \\ fs [MONAD_HASH_IO_def]
  \\ xlet `POSTv v.
       (W8ARRAY result (CFS message)  * IOx ev_ffi_part ev)`
  >| [
      xffi 
   \\ fs[cfHeapsBaseTheory.IOx_def,ev_ffi_part_def,IO_def]
   \\ xsimpl
   \\ qmatch_goalsub_abbrev_tac `FFI_part s u ns`
   \\ qexists_tac `MAP ((n2w:num -> word8) o ORD) (explode message)`
   \\ map_every qexists_tac [`emp`, `s`, `u`, `ns`, `events`]
   \\ xsimpl
   \\ unabbrev_all_tac
   \\ fs[] \\ rw[] \\ xsimpl
   \\ fs[MAP_MAP_o, wordsTheory.w2n_n2w, stringTheory.CHR_ORD, o_DEF, ORD_BOUND]
   \\ ASSUME_TAC explode_thm_1 >- metis_tac[STRING_TYPE_def]
   \\ Cases_on `mk_ffi_next (encode,decode,[("hash",ffi_hash)]) "hash"
            (MAP ((n2w :num -> word8 ) o ORD) (explode (message :mlstring)))
            (REPLICATE (32 :num) (0w :word8)) (encode (ev :IOhashFuns))`
   \\ rw[]
   \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_hash_def, 
      encode_mutable_def, encode_immutable_def,  GSYM cfHeapsBaseTheory.encode_list_def]
   \\ Cases_on `strlen message >= 32`
      >|
        [fs[],
         fs[] ,
         fs[] ,
         fs[] , 
         fs[] , 
         fs[] ]
      >|
         [xsimpl
          \\ qpat_abbrev_tac `new_events = events ++ _`
          \\ qexists_tac `new_events`, 
          xsimpl
          \\ qpat_abbrev_tac `new_events = events ++ _`
          \\ qexists_tac `new_events`,
          xsimpl
          \\ qpat_abbrev_tac `new_events = events ++ _`
          \\ qexists_tac `new_events`,
          xsimpl
          \\ qpat_abbrev_tac `new_events = events ++ _`
          \\ qexists_tac `new_events`]
      >|
         [fs[CFS_def] \\ xsimpl \\ fs[o_DEF], 
          fs[CFS_def] \\ xsimpl \\ fs[o_DEF],
          fs[CFS_def] \\ xsimpl \\ fs[o_DEF],
          fs[CFS_def] \\ xsimpl \\ fs[o_DEF]]
   ,  xapp
   \\ xsimpl 
   ]
QED

val calculate_from_string_def = Define `
  calculate_from_string m = (\cl. (Success (CFS m), cl) )`;

(* Eval env exp P is true 
   if exp evaluates (in environment env) 
   to some result res(of HOL type v) such 
   that P holds for res, i.e.P res.

Eval:"v sem_env -> exp -> (v -> bool) -> bool"

EvalM:"bool ->
    v sem_env ->
    α ->
    exp ->
    (α -> α # (v list, v) result -> bool) ->
    (α -> (heap_part -> bool) -> bool) #
    (β -> (string |-> ffi)) #
    (string list #
    (string -> word8 list -> word8 list -> ffi -> ffi ffi_result option))
    list -> bool"

The H in the definition above is a pair(h,p)
containing a heap assertion h and the projection p. 

MONAD:"(α -> v -> bool) ->
    (β -> v -> bool) ->
    (γ -> (α, β) exc # γ) -> γ -> γ # (v list, v) result -> bool"
*)

Theorem EvalM_calculate_from_string:
    Eval 
          env (* environment *)
          exp (* expression *)
          (STRING_TYPE m) /\ (nsLookup env.v (Long "HashFunction" (Short "calculate_from_string")) =
           SOME HashFunction_calculate_from_string_v) (* P *)
    ==>
    EvalM 
          F (* references only *)
          env (* environment *)
          stM (* state *)
          (App Opapp [Var (Long "HashFunction" (Short "calculate_from_string")); exp]) (* expression *)
      (MONAD (LIST_TYPE WORD8) exc_ty (calculate_from_string m)) (* P *)
      (MONAD_HASH_IO,p:'ffi ffi_proj) (* H *)
Proof
  ho_match_mp_tac EvalM_from_app \\ 
  rw [calculate_from_string_def,ffi_hash_def]
  \\ metis_tac [hash_basic_spec]
QED

fun  with_ffi hash_args commandline_name stdio_name (translator_config : config) =
  with_heap_propositions
    [(``MONAD_HASH_IO``, hash_args), (``MONAD_IO``, stdio_name), (``COMMANDLINE``, commandline_name)]
    translator_config
;
(*
fun with_ffi hash_args (translator_config : config) =
  with_heap_propositions
    [(``MONAD_HASH_IO``, hash_args)]
    translator_config;
*)
(*
 * Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Datatype:
  state_references = <| hashfunction : IOhashFuns
                      ; commandline  : mlstring list
                      ; stdio : IO_fs |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail
End

val config =  global_state_config |>
              with_state ``:state_references`` |>
              with_exception ``:state_exn`` |>
              with_ffi "hashfunction" "commandline" "stdio";


(* Initialize the translation *)
val _ = start_translation config;

val hd_def = Define `
  hd l = dtcase l of [] => raise_Fail | x::l' => return x`;

(*
val str_to_num_def = Define `
  str_to_num (s:mlstring) =
    dtcase mlint$fromString s of
      NONE => raise_Fail
    | SOME i => if i < 0i then raise_Fail else return (Num i)`;*)
(*
val str_to_mlstr_def = Define `
  str_to_mlstr l = return (implode l )`;
*)

val w8list_to_str_def = Define `
  w8list_to_str (x: word8 list) = implode (MAP (\b. CHR (w2n b)) x)`;

val monadic_w8list_to_str_def = Define `
  monadic_w8list_to_str l = return (w8list_to_str l )`;

val calculate_from_bytes_def = Define`
  calculate_from_bytes byte_msg =
    do
      (msg: mlstring) <- (monadic_w8list_to_str byte_msg);
      (lst: word8 list) <- (hashfunction (calculate_from_string msg)); 
      return (lst)
    od`;


val num_to_str_def = Define `
  num_to_str (n:num) = mlint$toString (& n)`;


(*
 val intlst = List.map (fn ch => Char.chr (Word8.toInt ch) ) hash 
 stdio (print (num_to_str ((w2n:word8 -> num) lstfst) ) ) ;
*)
val cfbm_def = Define`
  cfbm () =
    do
      (args:mlstring list) <- commandline (arguments ()) ;
      (msg:mlstring) <- hd args;
      (lst: word8 list) <- (hashfunction (calculate_from_string msg)); 
      stdio (print (w8list_to_str lst) ) ;
      stdio (print (strlit "\n"))
    od otherwise do
            name <- commandline (name ()) ;
            stdio (print_err (strlit"usage: " ^ name ^ strlit" <n>\n"))
          od`;


val res = m_translate hd_def;

val res = translate num_to_str_def;

val res = translate w8list_to_str_def;

(* DISCH_ALL res; *)

val w8list_to_str_side = Q.prove (
  `w8list_to_str_side v2 <=> T`,
  rw [fetch "-" "w8list_to_str_side_def"] >> fs [w2n_lt_256]
  )
  |> update_precondition;

val res = m_translate monadic_w8list_to_str_def;

(* val res = m_translate str_to_mlstr_def; *)

val res = m_translate calculate_from_bytes_def; 

val res = m_translate cfbm_def;


val _ = export_theory();

