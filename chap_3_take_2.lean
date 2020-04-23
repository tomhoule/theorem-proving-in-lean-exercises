
namespace ex1
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

    theorem implication_composition : (p → (q → r)) ↔ (p ∧ q → r) :=
    have left_to_right : (p → (q → r)) → (p ∧ q → r), from λ f₁, λ hpq, (f₁ hpq.left) hpq.right,
    have right_to_left : (p ∧ q → r) → (p → (q → r)), from λ f₁ hp hq, f₁ (and.intro hp hq),
    ⟨left_to_right, right_to_left⟩

    theorem disjunct_implications_decomposition : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    have left_to_right : ((p ∨ q) → r) → (p → r) ∧ (q → r), from λ f, and.intro (λ hp, f $ or.inl hp) (λ hq, f $ or.inr hq),
    have right_to_left : (p → r) ∧ (q → r) → ((p ∨ q) → r), from λ fs, λ hor, or.elim hor (λ hp, fs.left hp) (λ hq, fs.right hq),
    ⟨left_to_right, right_to_left⟩

    theorem de_morgan_disjunction : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    have left_to_right : ¬(p ∨ q) → ¬p ∧ ¬q, from λ hnpq, and.intro (λ hp, hnpq (or.inl hp)) (λ hq, hnpq (or.inr hq)),
    have right_to_left : ¬p ∧ ¬q → ¬(p ∨ q), from λ hnpq, assume p_or_q, or.elim p_or_q (λ hp, hnpq.left hp) (λ hq, hnpq.right hq),
    ⟨left_to_right, right_to_left⟩

    theorem disjunction_of_negations_implies_negation_of_conjunction : ¬p ∨ ¬q → ¬(p ∧ q) :=
        λ h, assume p_and_q, or.elim h (λ hnp, hnp p_and_q.left) (λ hnq, hnq p_and_q.right)

    theorem p_and_not_q_means_p_does_not_imply_q : p ∧ ¬q → ¬(p → q) := λ h, assume ptoq, absurd (ptoq h.left) h.right

    theorem p_or_false_equivalent_to_p : p ∨ false ↔ p :=
    have left_to_right : p ∨ false → p, from λ h, or.elim h (λ hp, hp) (λ ff, false.elim ff),
    have right_to_left : p → p ∨ false, from λ hp, or.inl hp,
    ⟨left_to_right, right_to_left⟩

    theorem p_and_false_equivalent_to_false : p ∧ false ↔ false :=
    have left_to_right : p ∧ false → false, from λ pair, pair.right,
    have right_to_left : false → p ∧ false, from λ f, false.elim f,
    ⟨left_to_right, right_to_left⟩

    theorem not_p_or_q_implies_p_implies_q : (¬p ∨ q) → (p → q) := λ h, λ hp, or.elim h (λ hnp, absurd hp hnp) (λ hq, hq)

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
    example : (p → (q → r)) ↔ (p ∧ q → r) := @implication_composition p q r
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := @disjunct_implications_decomposition p q r
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := @de_morgan_disjunction p q
    example : ¬p ∨ ¬q → ¬(p ∧ q) := @disjunction_of_negations_implies_negation_of_conjunction p q
    example : ¬(p ∧ ¬p) := @p_and_not_p_is_absurd p
    example : p ∧ ¬q → ¬(p → q) := @p_and_not_q_means_p_does_not_imply_q p q
    example : ¬p → (p → q) := assume hnp hp, absurd hp hnp
    example : (¬p ∨ q) → (p → q) := @not_p_or_q_implies_p_implies_q p q
    example : p ∨ false ↔ p := @p_or_false_equivalent_to_p p
    example : p ∧ false ↔ false := @p_and_false_equivalent_to_false p
    example : ¬(p ↔ ¬p) := @p_is_equivalent_to_not_p_is_absurd p
    example : (p → q) → (¬q → ¬p) := @implication_flips p q

end ex1

section ex2
    open classical

    variables p q r s : Prop

    theorem long (h : p → r ∨ s) : (p → r) ∨ (p → s) :=
    by_cases
        (λ hp : p,
            have r_or_s : r ∨ s, from h hp,
            or.elim r_or_s (λ hr : r, or.inl (λ hp, hr)) (λ hs : s, or.inr (λ hp, hs))
        )
        (λ hnp : ¬p, or.inl (λ hp : p, absurd hp hnp))

    theorem not_conjunction_implies_disjunction_of_nots (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    by_cases
        (λ hp : p, by_cases (λ hq : q, false.elim $ h (and.intro hp hq)) (λ hnq : ¬q, or.inr hnq))
        (λ hnp : ¬p, or.inl hnp)

    theorem nptoq_to_p_and_nq (h : ¬(p → q)) : p ∧ ¬q :=
    by_cases
        (λ hq : q,
            have p_to_q : p → q, from λ hp : p, hq,
            false.elim $ absurd p_to_q h
        )
        (λ hnq : ¬q,
            by_cases
                (λ hp : p, and.intro hp hnq)
                (λ hnp : ¬p,
                    have p_to_q : p → q, from λ hp, absurd hp hnp,
                    false.elim $ absurd p_to_q h
                )
        )

    theorem p_implies_q_implies_not_p_or_q (h : p → q) : (¬p ∨ q) :=
    or.elim (em p)
        (λ hp, or.inr (h hp))
        (λ hnp, or.inl hnp)

    theorem give_this_one_a_name (h : ¬q → ¬p) (hp : p) : q :=
    by_contradiction (
        λ hnq,
            have hnp : ¬p, from h hnq,
            absurd hp hnp
    )

    theorem last_one (h : (p → q) → p) : p :=
    or.elim (em p)
        (@id p)
        (λ hnp,
            have p_to_q : p → q, from λ hp, absurd hp hnp,
            show p, from h p_to_q
        )

    example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := @long p r s
    example : ¬(p ∧ q) → ¬p ∨ ¬q := @not_conjunction_implies_disjunction_of_nots p q
    example : ¬(p → q) → p ∧ ¬q := @nptoq_to_p_and_nq p q
    example : (p → q) → (¬p ∨ q) := @p_implies_q_implies_not_p_or_q p q
    example : (¬q → ¬p) → (p → q) := @give_this_one_a_name p q
    example : p ∨ ¬p := @em p
    example : (((p → q) → p) → p) := @last_one p q

end ex2

section ex3
    variable p : Prop

    example : ¬(p ↔ ¬p) := @ex1.p_is_equivalent_to_not_p_is_absurd p
end ex3
