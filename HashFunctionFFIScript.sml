open preamble
open cfHeapsBaseTheory

val _ = new_theory "HashFunctionFFI";

(* A small IO model *)
(* Create the data type to handle the references and I/O. *)
val _ = Datatype `
  IOhashFuns = <| immutable: word8 list;
                  mutable: (word8 # word8) list |>`;

val IOhashFuns_component_equality = theorem"IOhashFuns_component_equality";

val ffi_hash_def = Define `
  ffi_hash (conf:word8 list) (bytes:word8 list) (arg:IOhashFuns) =
    if LENGTH bytes = 32 then
      if LENGTH conf >=32 then
        SOME (FFIreturn (TAKE 32 conf) arg)
      else 
        SOME (FFIreturn (conf++(REPLICATE (32-(LENGTH conf)) (0w: word8))) arg)
    else
        NONE`;

val encode_immutable_def = Define`
  encode_immutable ev =  encode_list (Num o (w2n: word8 -> num)) ev`;

val encode_mutable_def = Define`
  encode_mutable ev =  encode_list (encode_pair (Num o (w2n: word8 -> num)) (Num o  (w2n: word8 -> num))) ev`;


val encode_def = Define `encode (ev:IOhashFuns) =
  Cons
    (encode_immutable ev.immutable)
    (encode_mutable ev.mutable)
`;

Theorem encode_mutable_11[simp]:
   !xs ys. (encode_mutable xs = encode_mutable ys) <=> (xs = ys)
Proof
  rw [] \\ eq_tac \\ rw [encode_mutable_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD]
  \\ rw [encode_mutable_def]
QED


Theorem encode_immutable_11[simp]:
   !xs ys. (encode_immutable xs = encode_immutable ys) <=> (xs = ys)
Proof
  rw [] \\ eq_tac \\ rw [encode_immutable_def]
  \\ drule encode_list_11
  \\ fs [encode_pair_def,FORALL_PROD]
  \\ rw [encode_immutable_def]
QED

Theorem encode_11[simp]:
   !x y. (encode x = encode y) <=> (x = y)
Proof
  fs [encode_def] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [IOhashFuns_component_equality]
QED

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val ev_ffi_part_def = Define`
  ev_ffi_part = (encode,decode,
    [("hash",ffi_hash)])`;

val _ = export_theory();

