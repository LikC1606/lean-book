/-!
# Chapter 15 — Mini authorization policy (deny overrides)
-/

namespace Examples.Ch15

inductive Action where
  | read
  | write
  | delete
deriving DecidableEq, Repr

structure Policy where
  allow : List Action
  deny : List Action
deriving Repr

def Policy.permits (p : Policy) (a : Action) : Bool :=
  if a ∈ p.deny then false
  else a ∈ p.allow

theorem deny_overrides (p : Policy) (a : Action) (h : a ∈ p.deny) :
    p.permits a = false := by
  simp [Policy.permits, h]

theorem allow_if_not_denied
    (p : Policy) (a : Action)
    (hd : a ∉ p.deny) (ha : a ∈ p.allow) :
    p.permits a = true := by
  simp [Policy.permits, hd, ha]

def demoPolicy : Policy where
  allow := [.read, .write]
  deny := [.delete]

#eval demoPolicy.permits .read
#eval demoPolicy.permits .delete

end Examples.Ch15
