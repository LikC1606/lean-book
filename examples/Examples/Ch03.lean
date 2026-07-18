/-!
# Chapter 3 — First steps

Runnable snippets from 《三十分钟上手 Lean 4》.
-/

namespace Examples.Ch03

#eval 1 + 2 * 3
#eval (5 : Float) / 2
#eval "Hello" ++ ", Lean!"
#eval List.range 5

def greet (name : String) : String :=
  s!"你好，{name}！欢迎来到 Lean 的世界。"

#eval greet "小明"

def add (a b : Nat) : Nat := a + b
#eval add 3 4
#eval [1, 2, 3, 4].map (add 100)

def describe : List Nat → String
  | [] => "空列表，什么都没有"
  | [x] => s!"只有一个元素：{x}"
  | x :: xs => s!"首元素是 {x}，后面还有 {xs.length} 个"

#eval describe [1, 2, 3]

def safeHead : List Nat → Option Nat
  | [] => none
  | x :: _ => some x

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval sum [1, 2, 3, 4, 5]

theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

example (n : Nat) : n + 0 = n := by simp
example (a b : Nat) : a + b = b + a := by omega

def contains : Nat → List Nat → Bool
  | _, [] => false
  | x, y :: ys => if x == y then true else contains x ys

#eval contains 3 [1, 2, 3, 4]

end Examples.Ch03
