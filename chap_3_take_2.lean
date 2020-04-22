
section ex1
    variables p q r : Prop

    -- >>> Proofs <<< --

    theorem and_commutes : p ∧ q ↔ q ∧ p :=
        iff.intro
            (λ pq, ⟨pq.right, pq.left⟩)
            (λ qp, ⟨qp.right, qp.left⟩)

    theorem or_commutes : p ∨ q ↔ q ∨ p :=
        iff.intro
            (λ pq, pq.elim (λ hp, or.inr hp) (λ hq, or.inl hq) )
            (λ qp, qp.elim (λ hq, or.inr hq) (λ hp, or.inl hp))


    theorem and_associates : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
        have ltr : (p ∧ q) ∧ r → p ∧ (q ∧ r), from λ hpqr, ⟨hpqr.left.left, ⟨hpqr.left.right, hpqr.right⟩⟩,
        have rtl : p ∧ (q ∧ r) → (p ∧ q) ∧ r, from λ hpqr, ⟨⟨hpqr.left, hpqr.right.left⟩, hpqr.right.right⟩ ,
        ⟨ltr, rtl⟩

    theorem or_associates : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
        let ltr := λ (h : (p ∨ q) ∨ r),
            h.elim
                (λ hpq, hpq.elim (λ hp, or.inl hp) (λ hq, or.inr (or.inl hq)))
                (λ hr, or.inr (or.inr hr)) in
        let rtl := λ (h : p ∨ (q ∨ r)),
            h.elim
                (λ hp, or.inl (or.inl hp))
                (λ hqr, hqr.elim (λ hq, or.inl (or.inr hq)) (λ hr, or.inr hr)) in
        ⟨ltr, rtl⟩

    theorem and_distributes : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    have left_to_right : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from
        λ h, and.elim h (λ hp hqr, hqr.elim (λ hq, or.inl ⟨hp, hq⟩) (λ hr, or.inr ⟨hp, hr⟩)),

    have right_to_left : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from
        λ h, or.elim h
            (λ hpq, ⟨hpq.left, or.inl hpq.right⟩)
            (λ hpr, ⟨hpr.left, or.inr hpr.right⟩),

    ⟨left_to_right, right_to_left⟩


    theorem or_distributes : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    have left_to_right : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from
        λ h, or.elim h
            (λ hp, ⟨or.inl hp, or.inl hp⟩)
            (λ hqr, ⟨or.inr hqr.left, or.inr hqr.right⟩),
    have right_to_left : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r), from
        λ h, and.elim h
            (λ h₁ h₂, h₁.elim (λ hp, or.inl hp) (λ hq, h₂.elim (λ hp, or.inl hp) (λ hr, or.inr ⟨hq, hr⟩))),
    ⟨left_to_right, right_to_left⟩

    theorem implication_flips (h : p → q) (hnq : ¬q): ¬p :=
    assume hp : p,
    absurd (h hp) hnq

    theorem p_and_not_p_is_absurd : ¬(p ∧ ¬p) :=
    assume h₁ : p ∧ ¬p,
    absurd h₁.left h₁.right


    -- negation is a powerful drug
    theorem p_is_equivalent_to_not_p_is_absurd : ¬(p ↔ ¬p) :=
    assume h,
    have p_implies_not_p : p → ¬p, from iff.elim_left h,
    have not_p_implies_p : ¬p → p, from iff.elim_right h,
    have hnp : ¬p, from λ hp : p, absurd hp (p_implies_not_p hp),
    absurd (not_p_implies_p hnp) hnp

    -- >>> Goals <<< --

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p := @and_commutes p q
    example : p ∨ q ↔ q ∨ p := @or_commutes p q

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := @and_associates p q r
    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := @or_associates p q r

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := @and_distributes p q r
    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := @or_distributes p q r

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
    example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
    example : ¬(p ∧ ¬p) := @p_and_not_p_is_absurd p
    example : p ∧ ¬q → ¬(p → q) := sorry
    example : ¬p → (p → q) := sorry
    example : (¬p ∨ q) → (p → q) := sorry
    example : p ∨ false ↔ p := sorry
    example : p ∧ false ↔ false := sorry
    example : ¬(p ↔ ¬p) := @p_is_equivalent_to_not_p_is_absurd p
    example : (p → q) → (¬q → ¬p) := @implication_flips p q

end ex1
