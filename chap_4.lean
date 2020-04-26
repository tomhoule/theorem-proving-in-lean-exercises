
namespace ex1
    -- Prove these equivalences:
    variables (α : Type) (p q : α → Prop)

    def proof1 : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    have left : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x), from
        assume h : (∀ x, p x ∧ q x),
        and.intro (λ z : α, (h z).left) (λ z : α, (h z).right),
    have right : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x), from
        assume h : (∀ x, p x) ∧ (∀ x, q x),
        λ z : α, and.intro (h.left z) (h.right z),
    ⟨left, right⟩

    def proof2 (h₁ : ∀ x, p x → q x) (h₂ : ∀ x, p x) : (∀ x, q x) :=
    λ z : α, (h₁ z) (h₂ z)

    def proof3 (h : (∀ x, p x) ∨ (∀ x, q x)) : ∀ x, p x ∨ q x :=
    λ z : α, or.elim h (λ hp, or.inl $ hp z) (λ hq, or.inr $ hq z)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := @proof1 α p q
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := @proof2 α p q
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := @proof3 α p q

    -- You should also try to understand why the reverse implication
    -- is not derivable in the last example.
    --
    -- Answer: difference between "for any instance of the type, p or q holds"
    -- (less general, right), and "p holds for any instance of the type, or q
    -- holds for any instance of the type" (more general, left). The xs could be
    -- different instances of α, since they are bound separately.
end ex1

namespace ex2

    variables (α : Type) (p q : α → Prop)
    variable r : Prop

    def proof1 (a : α) : ((∀ x : α, r) ↔ r) :=
    have left: ((∀ x : α, r) → r), from λ hx, hx a,
    have right : (r → (∀ x : α, r)), from λ hr, λ z, hr,
    ⟨left, right⟩

    def proof2 : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    have left : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r, from
        assume (h : ∀ x, p x ∨ r),
        or.elim (classical.em r)
            (λ hr, or.inr hr)
            (λ hnr, or.intro_left r (
                λ z : α, or.elim (classical.em (p z))
                    (λ hpz, hpz)
                    (λ hnpz, false.elim $ or.elim (h z) (λ hpz, absurd hpz hnpz) (λ hr, absurd hr hnr))
                )),
    have right : (∀ x, p x) ∨ r → (∀ x, p x ∨ r), from
        assume (h : (∀ x, p x) ∨ r),
        λ (z : α), or.elim h (λ hp, or.inl $ hp z) (λ hr, or.inr hr),
    ⟨left, right⟩

    def proof3 : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    have left : (∀ x, r → p x) → (r → ∀ x, p x), from
        assume (h : ∀ z : α, r → p z),
        λ (hr : r), λ (zz : α), h zz hr,
    have right : (r → ∀ x, p x) → (∀ x, r → p x), from
        assume (h : r → ∀ x, p x),
        λ (z : α), λ (hr :r), (h hr) z,
    ⟨left, right⟩

    example : α → ((∀ x : α, r) ↔ r) := proof1 α r
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := proof2 α p r
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := proof3 α p r

end ex2
