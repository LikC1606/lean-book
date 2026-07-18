/-!
# Chapter 4 — Functional programming

Expression evaluator mini-project.
-/

namespace Examples.Ch04

inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
deriving Repr, BEq

def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .neg a => -a.eval

def Expr.pretty : Expr → String
  | .num n => toString n
  | .add a b => s!"({a.pretty} + {b.pretty})"
  | .sub a b => s!"({a.pretty} - {b.pretty})"
  | .mul a b => s!"({a.pretty} * {b.pretty})"
  | .neg a => s!"(-{a.pretty})"

def exampleExpr : Expr :=
  .mul (.add (.num 1) (.num 2)) (.num 3)

#eval exampleExpr.eval
#eval exampleExpr.pretty

def myMap (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: myMap f xs

#eval myMap (· * 2) [1, 2, 3]

end Examples.Ch04
