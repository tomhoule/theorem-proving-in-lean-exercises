
section ex1
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
    -- (less general, right)), and "p holds for any instance of the type, or q
    -- holds for any instance of the type" (more general, left). The xs could be
    -- different instances of α, since they are bound separately.
end ex1
