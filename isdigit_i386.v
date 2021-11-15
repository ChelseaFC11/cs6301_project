Require Import Picinae_i386.
Require Import NArith.
Open Scope N.
Definition isdigit_i386 : program := fun _ a => match a with
(* 0x19d33: movl 0x4(%esp), %eax *)
| 32051 => Some (4,
  Move R_EAX (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) LittleE 4)
  )

(* 0x19d37: subl $0x30, %eax *)
| 32055 => Some (3, 
  Move (V_TEMP 3403 (* #26714 *)) (Cast CAST_LOW 32 (Var R_EAX)) $;
  Move R_EAX (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 48 32)) $;
  Move R_CF (BinOp OP_LT (Var (V_TEMP 3403 (* #26714 *))) (Word 48 32)) $;
  Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Var (V_TEMP 3403 (* #26714 *))) (Word 48 32)) (BinOp OP_XOR (Var (V_TEMP 3403 (* #26714 *))) (Cast CAST_LOW 32 (Var R_EAX))))) $;
  Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 3403 (* #26714 *)))) (Word 48 32)))) $;
  Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 10 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Cast CAST_LOW 32 (Var R_EAX)) (Word 4 32)) (Cast CAST_LOW 32 (Var R_EAX))) (Let (V_TEMP 9 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* $1 *))) (Word 2 32)) (Var (V_TEMP 10 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* $2 *))) (Word 1 32)) (Var (V_TEMP 9 (* $2 *)))))))) $;
  Move R_SF (Cast CAST_HIGH 1 (Cast CAST_LOW 32 (Var R_EAX))) $;
  Move R_ZF (BinOp OP_EQ (Word 0 32) (Cast CAST_LOW 32 (Var R_EAX)))
  )

(* 0x19d3a: cmpl $0x9, %eax *)
| 32058 => Some (3, 
  Move (V_TEMP 3404 (* #26717 *)) (BinOp OP_MINUS (Cast CAST_LOW 32 (Var R_EAX)) (Word 9 32)) $;
  Move R_CF (BinOp OP_LT (Cast CAST_LOW 32 (Var R_EAX)) (Word 9 32)) $;
  Move R_OF (Cast CAST_HIGH 1 (BinOp OP_AND (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Word 9 32)) (BinOp OP_XOR (Cast CAST_LOW 32 (Var R_EAX)) (Var (V_TEMP 3404 (* #26717 *)))))) $;
  Move R_AF (BinOp OP_EQ (Word 16 32) (BinOp OP_AND (Word 16 32) (BinOp OP_XOR (BinOp OP_XOR (Var (V_TEMP 3404 (* #26717 *))) (Cast CAST_LOW 32 (Var R_EAX))) (Word 9 32)))) $;
  Move R_PF (UnOp OP_NOT (Cast CAST_LOW 1 (Let (V_TEMP 10 (* $1 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 3404 (* #26717 *))) (Word 4 32)) (Var (V_TEMP 3404 (* #26717 *)))) (Let (V_TEMP 9 (* $2 *)) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 10 (* $1 *))) (Word 2 32)) (Var (V_TEMP 10 (* $1 *)))) (BinOp OP_XOR (BinOp OP_RSHIFT (Var (V_TEMP 9 (* $2 *))) (Word 1 32)) (Var (V_TEMP 9 (* $2 *)))))))) $;
  Move R_SF (Cast CAST_HIGH 1 (Var (V_TEMP 3404 (* #26717 *)))) $;
  Move R_ZF (BinOp OP_EQ (Word 0 32) (Var (V_TEMP 3404 (* #26717 *))))
  )

(* 0x19d3d: setbe %al *)
| 32061 => Some (3,
  Move R_EAX (Concat (Extract 31 8 (Var R_EAX)) (Cast CAST_UNSIGNED 8 (BinOp OP_OR (Var R_CF) (Var R_ZF))))
  )

(* 0x19d40: movzbl %al, %eax *)
| 32064 => Some (3,
  Move R_EAX (Cast CAST_UNSIGNED 32 (Cast CAST_LOW 8 (Var R_EAX)))
  )

(* 0x19d43: retl *)
| 32067 => Some (1, 
  Move (V_TEMP 3405 (* #26719 *)) (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
  Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
  Jmp (Var (V_TEMP 3405 (* #26719 *)))
  )
  
| _ => None
end.
  