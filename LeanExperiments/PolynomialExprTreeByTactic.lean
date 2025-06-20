import Mathlib

open Polynomial

namespace Tactic.Gcd
open Lean Elab Tactic Meta Expr Qq

inductive Poly
  | const : ℚ → Poly
  | var : ℕ → Poly
  | add : Poly → Poly → Poly
  | sub : Poly → Poly → Poly
  | mul : Poly → Poly → Poly
  | smul : ℚ → Poly → Poly
  | pow : Poly → ℕ → Poly
  | neg : Poly → Poly
  deriving BEq, Repr

def Poly.format : Poly → Lean.Format
  | .const c => f!"{c}"
  | .var n => f!"x{n}"
  | .add a b => f!"({a.format} + {b.format})"
  | .sub a b => f!"({a.format} - {b.format})"
  | .mul a b => f!"({a.format} * {b.format})"
  | .smul s a => f!"({s} * {a.format})"
  | .pow a n => f!"({a.format} ^ {n})"
  | .neg a => f!"(- {a.format})"

/-- Typesafe conversion of `n : ℕ` to `Q($α)`. -/
def ofNatQ {u : Level} (α : Q(Type u)) (_ : Q(Semiring $α)) (n : ℕ) : Q($α) :=
  match n with
  | 0 => q(0 : $α)
  | 1 => q(1 : $α)
  | k+2 =>
    have lit : Q(ℕ) := mkRawNatLit n
    have k : Q(ℕ) := mkRawNatLit k
    haveI : $lit =Q $k + 2 := ⟨⟩
    q(OfNat.ofNat $lit)

def Poly.toPolynomial {u : Level} {R : Q(Type u)} (inst : Q(Field $R)) : Poly → Option Q($R[X])
  | .const c =>
      let c_num : Q($R) := ofNatQ R inst c.num.toNat
      let c_den : Q($R) := ofNatQ R inst c.den
      some q(C ($c_num / $c_den : «$R»))
  | .var n =>
    if n != 0 then none else some q(X)
  | .add a b =>
    match (a.toPolynomial inst, b.toPolynomial inst) with
    | (some a, some b) => some q($a + $b)
    | _ => none
  | .sub a b =>
    match (a.toPolynomial inst, b.toPolynomial inst) with
    | (some a, some b) => some q($a + $b)
    | _ => none
  | .mul a b =>
    match (a.toPolynomial inst, b.toPolynomial inst) with
    | (some a, some b) => some q($a * $b)
    | _ => none
  | .smul s a =>
    (a.toPolynomial inst).map fun a =>
      let s_num : Q($R) := ofNatQ R inst s.num.toNat
      let s_den : Q($R) := ofNatQ R inst s.den
      q(($s_num / $s_den : $R) •$a)
  | .pow a n =>
    (a.toPolynomial inst).map fun a =>
      let n : Q(ℕ) := Qq.ofNatQ q(ℕ) q(inferInstance) n
      q($a ^ $n)
  | _ => none

#check 1 + 2

#check (-1/2 : ℚ)

instance : ToFormat Poly := {
  format := Poly.format
}

set_option trace.Meta.synthInstance true in
#check (inferInstance : ToFormat (List ℕ))

open Mathlib.Meta in
partial def parse {u : Level} {R : Q(Type u)} (inst : Q(Ring $R)) (expr : Q($R[X])) :
    MetaM Poly := do
  match expr with
  | ~q(X) => pure <| Poly.var 0
  | ~q($a + $b) => pure <| Poly.add (← parse inst a) (← parse inst b)
  -- | ~q($a - $b) => pure <| Poly.sub (← parse inst a) (← parse inst b)
  | ~q($a * $b) => pure <| Poly.mul (← parse inst a) (← parse inst b)
  | ~q($a ^ ($n : ℕ)) =>
    let n ← try
        let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
        pure n.natLit!
      catch _ =>
        pure n.natLit!
    pure <| Poly.pow (← parse inst a) n
  | ~q((($n : ℕ) : «$R»[X])) =>
    let n ←
      try
        let .isNat _ n _ ← NormNum.derive (α := q(ℕ)) n | failure
        pure n.natLit!
      catch _ =>
        pure n.natLit!
    pure <| Poly.const n
  | ~q(($s : «$R»[X]) • $a) => -- should not happen after `norm_num`
    pure <| Poly.mul (← parse inst s) (← parse inst a)
  | ~q(($s : «$R») • $a) =>
    let s ←
      try
        let a := ← (← NormNum.derive (α := R) s).toRat.getM
        pure a
      catch _ =>
        match s.rat? with
        | some s => pure s
        | none => throwError "what is {s}?"
    pure <| Poly.smul s (← parse inst a)
  | ~q(($s : ℕ) • $a) => -- should not happen after `norm_num`
    let s ← try
        let .isNat _ s _ ← NormNum.derive (α := q(ℕ)) s | failure
        pure s.natLit!
      catch _ =>
        pure s.natLit!
    pure <| Poly.smul s (← parse inst a)
  | ~q(-$a) => pure <| Poly.neg <| ← parse inst a
  | _ => throwError "unsupported expr {expr} as polynomial over {R}"

#check ((1 / 2 : ℚ[X]) • X ^ 3  + X: ℚ[X])



#eval parse q(inferInstance : Ring ℚ) q((9 / 2 : ℚ) • X ^ 3  + X: ℚ[X])

elab "explore" : tactic => do
  -- evalTactic <| ← `(tactic | try norm_num)
  let mvarId ← Lean.Elab.Tactic.getMainGoal
  -- let metavarDecl : MetavarDecl ← mvarId.getDecl
  if let .some (~q(@Eq (@Polynomial $R ($instSemiring)) (@gcd _ _ (_) $a1 $a2) $b))
      ← checkTypeQ (← mvarId.getType'') q(Prop) then
    let polyType : Q(Type u_1) := q(@Polynomial $R $instSemiring)
    let instRing ← synthInstanceQ q(Ring $R)
    let polyHAdd : Q(«$polyType» → «$polyType» → «$polyType») := q(HAdd.hAdd)
    let polyHMul : Q(«$polyType» → «$polyType» → «$polyType») := q(HMul.hMul)
    let polyPow : Q(«$polyType» → ℕ → «$polyType») := q(HPow.hPow)

    let a1 := ← parse (R := R) instRing a1
    let a2 := ← parse (R := R) instRing a2
    let b := ← parse (R := R) instRing b
    dbg_trace "got"
    Lean.logInfo f!"{a1}"
  else
    throwError "the goal isn't gcd a b = c"

variable {R : Type*} [Semiring R]

-- set_option trace.Meta.synthInstance true
-- #check (fun (x : ℕ) => (OfNat.ofNat x : Polynomial R))
end Tactic.Gcd

example :
    gcd ((X : ℚ[X]) • X ^ 3  + X: ℚ[X])
        ((1 / 3  + 1 / 2: ℚ) • X ^ 2 : ℚ[X]) =
      (X ^ 2 : ℚ[X]) := by
  -- norm_num
  explore
  sorry

-- example :
--     gcd (2 • X ^ 3 : ℕ[X])p
--         ((1 / 3  + 1 / 2: ℕ) • X ^ 2 : ℕ[X]) =
--       (X ^ 2 : ℕ[X]) := by
--   explore
--   sorry

-- example :
--     gcd ((1 / 3 : ℚ) • 3 * X ^ 3 - 2• X ^ 2 - X + 2 : ℚ[X])
--         ((X ^ 2 - 1) * (X ^ 4 + C (9 / 4 : ℚ)) - X ^ 3 - 1 : ℚ[X]) =
--       (X + 1 : ℚ[X]) := by
--   explore
--   sorry

-- example :
--     gcd ((1 / 3 : ℚ) • 3 * X ^ 3 - 2• X ^ 2 - X + 2 : ℚ[X])
--         ((X ^ 2 - 1) * (X ^ 4 + C (9 / 4 : ℚ)) - X ^ 3 - 1 : ℚ[X]) =
--       (X + 1 : ℚ[X]) := by
--   explore
--   sorry

#check Lean.Meta.whnfImp
#check ℕ
#check (1 : ℚ[X])

#check (1 : ℚ[X])
#check (gcd (α:=ℚ[X]))
#check Submodule.span_insert
