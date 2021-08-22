open preamble basis basisProgTheory
open ml_monad_translator_interfaceLib
open HashFunctionFFITheory HashFunctionProofTheory
open compilationLib

val _ = new_theory "HashFunctionCompile";

val _ = translation_extends"HashFunctionProof";

val _ = (append_prog o process_topdecs) `
    fun main () = cfbm();
`;

val maincall =``Dlet 
(Locs <|row := 0; col := 0; offset :=0 |> <|row := 0; col := 0; offset :=0 |>) 
(Pcon NONE []) (App Opapp [Var (Short "main"); Con NONE []])``;

val state = get_ml_prog_state();
val prog_tm = get_prog (remove_snocs(clean_state(state)));
val final_prog = ``SNOC ^maincall ^prog_tm``;
val prog_def = Define `out_prog = ^final_prog`;
(* load "compilationLib"; *)
val base_compiled = save_thm("hash_compiled", compile_x64 "hash" prog_def);



(*
val file = "full.sml";

fun read (infile : string) = let 
  val ins = TextIO.openIn infile; 
  fun loop ins = 
    case TextIO.inputLine ins of 
      SOME line => line ^ loop ins 
      | NONE => "" 
in 
  loop ins before TextIO.closeIn ins 
end;

val cakeml_code = (read file); 

val _ = (append_prog o process_topdecs) `^cakeml_code `;
val maincall =``Dlet 
(Locs <|row := 0; col := 0; offset :=0 |> <|row := 0; col := 0; offset :=0 |>) 
(Pcon NONE []) (App Opapp [Var (Short "main"); Con NONE []])``;

val state = get_ml_prog_state();
val prog_tm = get_prog (remove_snocs(clean_state(state)));
val final_prog = ``SNOC ^maincall ^prog_tm``;
val prog_def = Define `out_prog = ^final_prog`;
val base_compiled = save_thm("hash_compiled", compile_x64 "hash" prog_def);

*)

val _ = export_theory ();
