-- Exercise 1

section ex1

variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
have beep : p ∧ q → q ∧ p, from λ p_and_q : p ∧ q, and.intro p_and_q.2 p_and_q.1,
have boop : q ∧ p → p ∧ q, from λ q_and_p : q ∧ p, and.intro q_and_p.2 q_and_p.1,
show p ∧ q ↔ q ∧ p, from iff.intro beep boop

example : p ∨ q ↔ q ∨ p :=
have beep : p ∨ q → q ∨ p, from λ p_or_q : p ∨ q,
    or.elim
        p_or_q
        (or.intro_right q)
        (or.intro_left p),
have boop : q ∨ p → p ∨ q, from λ q_or_p : q ∨ p,
    or.elim
        q_or_p
        (or.intro_right p)
        (or.intro_left q),
show p ∨ q ↔ q ∨ p, from iff.intro beep boop

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
have group_left : (p ∧ q) ∧ r → p ∧ (q ∧ r), from (
    λ (left_grouped: (p ∧ q) ∧ r),
    and.intro
        left_grouped.elim_left.elim_left
        (and.intro left_grouped.elim_left.elim_right left_grouped.elim_right)
),
have group_right : p ∧ (q ∧ r) → (p ∧ q) ∧ r, from (
    λ (right_grouped: p ∧ (q ∧ r)),
    and.intro
        (and.intro right_grouped.elim_left right_grouped.elim_right.elim_left)
        right_grouped.elim_right.elim_right
),
show (p ∧ q) ∧ r ↔ p ∧ (q ∧ r), from iff.intro group_left group_right


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
have flattened_left : (p ∨ q) ∨ r → p ∨ q ∨ r, from (
    λ grouped, or.elim grouped
        (λ group,
            or.elim group
                (λ (hp : p), or.inl hp)
                (λ (hq : q), or.inr (or.inl hq))
            )
        (λ (hr : r), or.inr (or.inr hr))
),
have unflattened_left : p ∨ q ∨ r → (p ∨ q) ∨ r, from (
    λ flat, or.elim flat
        (λ (hp : p), or.inl (or.inl hp))
        (λ (hqr : q ∨ r), or.elim hqr
            (λ (hq : q), or.inl (or.inr hq))
            (λ (hr : r), or.inr hr)
        )
),
have flattened_right : p ∨ (q ∨ r) → p ∨ q ∨ r, from λ a, a,
have unflattened_right : p ∨ q ∨ r → p ∨ (q ∨ r), from λ a, a,
have left_flattens : (p ∨ q) ∨ r ↔ p ∨ q ∨ r, from iff.intro flattened_left unflattened_left,
have right_flattens : p ∨ (q ∨ r) ↔ p ∨ q ∨ r, from iff.intro flattened_right unflattened_right,
show (p ∨ q) ∨ r ↔ p ∨ (q ∨ r), from iff.trans left_flattens right_flattens


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
have expansion : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from (
    λ factorized,
    let (hp : p) := factorized.left in
    let (q_or_r_hypothesis : q ∨ r) := factorized.right in
    let (first_branch : q → (p ∧ q) ∨ (p ∧ r)) := λ hq,  or.intro_left (p ∧ r) (and.intro hp hq) in
    let (second_branch : r → p ∧ q ∨ p ∧ r) := λ hr, or.intro_right (p ∧ q) (and.intro hp hr) in
    or.elim
        q_or_r_hypothesis
        first_branch
        second_branch
),
have factorization : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from (
    λ expanded,
    let (hp : p) := or.elim expanded and.left and.left in
    let (extract_q : (p ∧ q) → (q ∨ r)) := λ p_and_q, or.intro_left r (and.right p_and_q) in
    let (extract_r : (p ∧ r) → (q ∨ r)) := λ p_and_r, or.intro_right q (and.right p_and_r) in
    let (q_or_r_hypothesis : q ∨ r) := or.elim expanded extract_q extract_r in
    and.intro hp q_or_r_hypothesis
),
show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r), from iff.intro expansion factorization



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
have expansion : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from (
    λ factorized,
    let (p_or_q : (p ∨ q)) := or.elim factorized (or.intro_left q) (λ conj, or.intro_right p conj.left) in
    let (p_or_r : (p ∨ r)) := or.elim factorized (or.intro_left r) (λ conj, or.intro_right p conj.right) in
    and.intro p_or_q p_or_r
),
have factorization : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r), from (
    λ expanded,
    let (p_case : p → p ∨ (q ∧ r)) := λ (hp : p), or.intro_left (q ∧ r) hp in
    let (q_and_r_case : (q ∧ r) → p ∨ (q ∧ r)) := λ (q_and_r : q ∧ r), or.intro_right p q_and_r in
    let split := λ (p_or_q : p ∨ q) (p_or_r : p ∨ r),
        or.elim p_or_q p_case (λ hq, or.elim p_or_r p_case (λ hr, q_and_r_case (and.intro hq hr))) in
    let (analyzed : p ∨ (q ∧ r)) := and.elim expanded split in
    or.elim analyzed p_case q_and_r_case
),
show p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r), from iff.intro expansion factorization

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
have implication : (p → (q → r)) → (p ∧ q → r), from λ p_to_q_to_r, λ p_and_q, p_to_q_to_r p_and_q.left p_and_q.right,
have reversed :  (p ∧ q → r) → (p → (q → r)), from λ p_and_q_to_r, λ p, λ q, p_and_q_to_r (and.intro p q),
show (p → (q → r)) ↔ (p ∧ q → r), from iff.intro implication reversed

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
have expansion : ((p ∨ q) → r) → (p → r) ∧ (q → r), from (
    λ p_or_q_to_r,
        and.intro
            (λ hp, let p_or_q := or.intro_left q hp in p_or_q_to_r p_or_q)
            (λ hq, let p_or_q := or.intro_right p hq in p_or_q_to_r p_or_q)
),
have factorization : (p → r) ∧ (q → r) → ((p ∨ q) → r), from (
    λ p_to_r_and_q_to_r, λ p_or_q, and.elim p_to_r_and_q_to_r (λ p_to_r q_to_r, or.elim p_or_q p_to_r q_to_r)
),
show ((p ∨ q) → r) ↔ (p → r) ∧ (q → r), from iff.intro expansion factorization


-- de morgan disjunction
def de_morgan_disjunction : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
have left_to_right : ¬(p ∨ q) → ¬p ∧ ¬q, from (
    assume not_p_or_q,
    and.intro
        (λ hnotp, not_p_or_q (or.inl hnotp))
        (λ hnotq, not_p_or_q (or.inr hnotq))
),
have right_to_left : ¬p ∧ ¬q → ¬(p ∨ q), from (
    λ not_p_and_not_q, not.intro (λ p_or_q, or.elim p_or_q (λ hp, not_p_and_not_q.left hp) (λ hq, not_p_and_not_q.right hq))
),
show ¬(p ∨ q) ↔ ¬p ∧ ¬q, from iff.intro left_to_right right_to_left

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := @de_morgan_disjunction p q


example : ¬p ∨ ¬q → ¬(p ∧ q) := λ not_p_or_not_q,
    not.intro (
        λ p_and_q,
        and.elim p_and_q (λ hp hq, or.elim not_p_or_not_q (λ not_p, not_p hp) (λ not_q, not_q hq))
    )


example : ¬(p ∧ ¬p) := λ conjunction, absurd conjunction.1 conjunction.2

example : p ∧ ¬q → ¬(p → q) :=
assume (p_and_not_q : p ∧ ¬q),
have hp : p, from p_and_not_q.left,
have nq : ¬q, from p_and_not_q.right,
show ¬(p → q), from not.intro (λ p_to_q, absurd (p_to_q hp) nq)

example : ¬p → (p → q) := λ (np : ¬p), λ (hp : p), absurd hp np

example : (¬p ∨ q) → (p → q) :=
λ not_p_or_q,
λ hp,
or.elim not_p_or_q (λ not_p, absurd hp not_p) (λ hq, hq)

example : p ∨ false ↔ p :=
have p_or_false_implies_p : (p ∨ false) → p, from (
    λ p_or_false, or.elim p_or_false (λ hp, hp) false.elim
),
have p_implies_p_or_false : p → (p ∨ false), from (
    λ hp, or.intro_left false hp
),
show p ∨ false ↔ p, from iff.intro p_or_false_implies_p p_implies_p_or_false

example : p ∧ false ↔ false :=
have p_and_false_implies_false : (p ∧ false) → false, from and.right,
have false_implies_p_and_false : false → (p ∧ false), from false.elim,
show p ∧ false ↔ false, from iff.intro p_and_false_implies_false false_implies_p_and_false


example : ¬(p ↔ ¬p) := @not.intro (p ↔ ¬p) (
    assume p_iff_not_p : p ↔ ¬p,
    have hnp : ¬p, from (
        assume hp : p,
        have not_p : ¬p, from iff.elim_left p_iff_not_p hp,
        show false, from absurd hp not_p
    ),
    have hp : p, from iff.elim_right p_iff_not_p hnp,
    show false, from absurd hp hnp
)

example : (p → q) → (¬q → ¬p) :=
λ (hpq : p → q), λ (nq : ¬q), not.intro (λ hp, absurd (hpq hp) nq)

end ex1

-- Exercize 2
section ex2
    open classical

    variables p q r s : Prop


    example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    assume p_to_r_or_s : p → r ∨ s,
    -- assume hp : p,
    -- have r_or_s : r ∨ s, from p_to_r_or_s hp,
    sorry

    -- de morgan conjunction
    example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume npandq : ¬(p ∧ q),
    by_contradiction (
        assume hno : ¬(¬p ∨ ¬q),
        have transformed : Π p₁ q₁, ¬(¬p₁ ∨ ¬q₁) → (¬p₁ ∧ ¬q₁), from λ l, iff.elim_left de_morgan_disjunction l
        -- have hdm : ¬p ∧ ¬q, from (iff.elim_left de_morgan_disjunction hno),
        sorry
    )

    example : ¬(p → q) → p ∧ ¬q :=
    assume h : ¬(p → q),
    sorry


    example : (p → q) → (¬p ∨ q) :=
    assume p_implies_q : p → q,
    sorry


    example : (¬q → ¬p) → (p → q) :=
    assume not_q_to_not_p : ¬q → ¬p,
    assume hp : p,
    sorry

    example : p ∨ ¬p := @em p

    example : (((p → q) → p) → p) :=
    assume p_implies_q_implies_p : ((p → q) → p),
    sorry

end ex2
