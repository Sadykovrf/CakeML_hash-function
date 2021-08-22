open preamble
open basis
open basisProgTheory
open ml_translatorLib
open ml_progLib
open ml_translatorTheory
open integerTheory
open cfDivTheory
open cfDivLib
open cfMonadTheory

val _ = new_theory "HashFunctionProg";

(* val _ = translation_extends"Word8ArrayProg"; *)
val _ = translation_extends "basisProg";

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = ml_prog_update (open_module "HashFunction");

val foo_def = Define`
  foo : char -> word8 = (\ch. n2w (ORD ch))`;

val foo_res = translate foo_def;

val cwl = (append_prog o process_topdecs) `
  fun convertW8Array2List a =
      List.map (foo) 
      (String.explode 
              (Word8Array.substring a 0 (Word8Array.length a))
      );`;

fun xcf' s = xcf_with_def ("HashFunction." ^ s) 
             (DB.fetch "HashFunctionProg" ("HashFunction_" ^ s ^ "_v_def"));

val lstmapthm = ListProgTheory.map_1_v_thm |> INST_TYPE [alpha |-> ``:word8``, beta |-> ``:char``];

Theorem convertW8Array2List_spec:
     !a. app (p:'ffi ffi_proj) HashFunction_convertW8Array2List_v [av]
     (W8ARRAY av a)
     (POSTv v.  & LIST_TYPE WORD8 a v * W8ARRAY av a) 
Proof
xcf' "convertW8Array2List"
   \\ rpt (xlet_auto THEN1 xsimpl) 
   >> (xapp_spec (lstmapthm)
   \\ xsimpl)
   \\ map_every qexists_tac [`(MAP (CHR o (w2n :word8 -> num )) (a :word8 list))`,
                             `foo`,
                              `WORD8`, 
                              `CHAR`]
   \\ rw[] \\ rw[foo_res] 
   \\ fs[MAP_MAP_o, o_DEF, foo_def, wordsTheory.w2n_n2w, stringTheory.CHR_ORD, ORD_BOUND]
QED

val sz =  (append_prog o process_topdecs) `
   fun size () = 32;`;

Theorem size_func_correct:
  !uv. (uv = Conv NONE []) ==>  app (p:'ffi ffi_proj) HashFunction_size_v [uv]
     emp
     (POSTv v. & NUM 32 v)
Proof
  xcf' "size" 
  \\ xmatch \\ xret \\ xsimpl
QED

val fl =  (append_prog o process_topdecs) `
   fun fill value = Word8Array.array (size ()) (Word8.fromInt value);`;

Theorem fill_func_correct:
  !u uv. NUM u uv ==>  app (p:'ffi ffi_proj) HashFunction_fill_v [uv]
     emp
     (POSTv v. W8ARRAY v (REPLICATE 32 ((n2w u):word8)) )
Proof
  xcf' "fill"
  \\ (xlet_auto THEN1 xsimpl) \\ xlet_auto 
  >| [ xcon THEN1 xsimpl, xlet_auto \\ xsimpl
     \\ xapp \\ rw[] ] 
QED

val zr =  (append_prog o process_topdecs) `
   fun zero () = Word8Array.array (size ()) (Word8.fromInt 0);`;

Theorem zero_func_correct:
   !uv. (uv = Conv NONE []) ==>  app (p:'ffi ffi_proj) HashFunction_zero_v [uv]
     emp
     (POSTv v. W8ARRAY v (REPLICATE 32 (0w :word8)) )
Proof
  xcf' "zero"
  \\ xmatch
  \\ (xlet_auto THEN1 xsimpl) \\ xlet_auto 
  >| [ xcon THEN1 xsimpl, xlet_auto THEN1 xsimpl
     \\ xapp \\ rw[] ] 
QED

val calculate_from_string_func = process_topdecs `
   fun calculate_from_string message =
          let
            val result = Word8Array.array (size ()) (Word8.fromInt 0)
          in
            (#(hash) message result; convertW8Array2List result)
          end;`;

val _ = append_prog calculate_from_string_func;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();

