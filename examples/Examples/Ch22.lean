/-!
# Chapter 22 — Verified stack calculator compiler
-/

namespace Examples.Ch22

inductive Instr where
  | push (n : Int)
  | add
  | mul
  | sub
deriving Repr

abbrev Stack := List Int
abbrev Prog := List Instr

def execInstr : Instr → Stack → Option Stack
  | .push n, s => some (n :: s)
  | .add, x :: y :: s => some ((y + x) :: s)
  | .mul, x :: y :: s => some ((y * x) :: s)
  | .sub, x :: y :: s => some ((y - x) :: s)
  | _, _ => none

def run : Prog → Stack → Option Stack
  | [], s => some s
  | i :: is, s =>
    match execInstr i s with
    | some s' => run is s'
    | none => none

inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
deriving Repr

def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .sub a b => a.eval - b.eval

def compile : Expr → Prog
  | .num n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]
  | .sub a b => compile a ++ compile b ++ [.sub]

theorem run_append (p q : Prog) (s : Stack) :
    run (p ++ q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    simp only [List.cons_append, run]
    cases execInstr i s with
    | none => rfl
    | some s' => exact ih s'

theorem compile_correct (e : Expr) (s : Stack) :
    run (compile e) s = some (e.eval :: s) := by
  induction e generalizing s with
  | num n =>
      simp [compile, run, execInstr, Expr.eval]
  | add a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr, Expr.eval]
  | mul a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr, Expr.eval]
  | sub a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr, Expr.eval]

def demo : Expr := .mul (.add (.num 1) (.num 2)) (.num 3)

#eval Expr.eval demo
#eval run (compile demo) []

#print axioms compile_correct

end Examples.Ch22
