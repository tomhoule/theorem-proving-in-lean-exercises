
section chap3ex1
    variables p q r : Prop

    example : p ∧ q ↔ q ∧ p :=
    begin
        apply iff.intro,
        repeat {
          intro h,
            exact and.intro h.right h.left,
        }
    end

    example : p ∨ q ↔ q ∨ p :=
    begin
        apply iff.intro,
          intro h,
          apply or.elim h,
            intro hp,
            right, exact hp,
            intro hq,
            left, exact hq,
        intro h,
        apply or.elim h,
          intro hp,
          right, exact hp,
        intro hq,
        left, exact hq
    end

    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    begin
        apply iff.intro,
        intro h,
        exact and.intro h.left.left ⟨h.left.right, h.right⟩,
        intro h,
        exact and.intro ⟨h.left, h.right.left⟩ h.right.right
    end

    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    begin
        apply iff.intro,
        { intro h,
          cases h with hpq hr,
          { cases hpq with hp hq,
            { left, assumption },
            { right, left, assumption }},
          { right, right, exact hr }},
        intro h,
        cases h with hp hqr,
        { left, left, exact hp },
        { cases hqr with hq hr,
          { left, right, exact hq },
          { right, exact hr }}
    end

    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    begin
        apply iff.intro,
        { intro h,
          have hp : p, from h.left,
          have hqr : q ∨ r, from h.right,
          cases hqr with hq hr,
          { left, constructor, assumption, assumption },
          right, constructor, assumption, assumption },
        intro h,
        cases h with hpq hpr,
          { constructor, exact hpq.left, left, exact hpq.right },
        constructor, exact hpr.left, right, exact hpr.right
    end

    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    begin
      apply iff.intro,
      { intro h,
        cases h with hp hqr,
        { constructor, repeat { left, exact hp } },
        { constructor; right, exact hqr.left, exact hqr.right } },
      intro h,
      have pq : p ∨ q, from h.left,
      have pr : p ∨ r, from h.right,
      cases pq with hp hq,
      { left, exact hp },
      have hq : q, from hq,
      cases pr with hp hr,
      { left, exact hp },
      right, constructor, exact hq, exact hr
    end

    example : (p → (q → r)) ↔ (p ∧ q → r) :=
    begin
      apply iff.intro,
      { intros h1 h2, exact h1 h2.left h2.right  },
      intros h1 hp hq,
      have pq : p ∧ q, { constructor, repeat { assumption }},
      exact h1 pq
    end

    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    begin
      apply iff.intro,
      { intro h,
        constructor ;
        { intro h1,
          have pq : p ∨ q, { { left, exact h1 } <|> { right, exact h1 } },
          exact h pq }},
      intros h1 h2,
      cases h2 with hp hq,
        exact h1.left hp,
      exact h1.right hq
    end

    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    begin
      apply iff.intro,
      { intro hnpq,
        constructor ;
        { intro h1,
          have hpq : p ∨ q, { { left <|> right, exact h1 } <|> { right, exact h1 } },
          exact absurd hpq hnpq }},
      intros h hc,
      have hnp : ¬ p, from h.left,
      have hnq : ¬ q, from h.right,
      cases hc with hp hq;
      { apply absurd, exact hp <|> exact hq, assumption}
    end

    example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    begin
      intros hdis hconj,
      cases hdis with hnp hnq,
        { exact absurd hconj.left hnp },
      exact absurd hconj.right hnq
    end

    example : ¬(p ∧ ¬p) :=
    begin
      intro h,
      exact absurd h.left h.right
    end

    example : p ∧ ¬q → ¬(p → q) :=
    begin
      intros hconj hn,
      have hq : q, { exact hn hconj.left },
      exact absurd hq hconj.right
    end

    example : ¬p → (p → q) :=
    begin
      intros hnp hp,
      exact (false.elim $ hnp hp)
    end

    example : (¬p ∨ q) → (p → q) :=
    begin
      intros hdis hp,
      cases hdis with hnp hq,
      { exact absurd hp hnp },
      assumption
    end

    example : p ∨ false ↔ p :=
    begin
      apply iff.intro,
      { intro h, cases h with hp hfalse, assumption, exact false.elim hfalse },
      intro hp, left, exact hp
    end

    example : p ∧ false ↔ false :=
    begin
      apply iff.intro,
      { intro h, exact h.right },
      intro hfalse, exact false.elim hfalse
    end

    example : ¬(p ↔ ¬p) :=
    begin
      intro h,
      have l : p → ¬p, { exact iff.elim_left h },
      have r : ¬p → p, { exact iff.elim_right h },
      have hnp : ¬p, { intro hp, exact absurd hp (l hp) },
      exact absurd (r hnp) hnp,
    end

    example : (p → q) → (¬q → ¬p) :=
    begin
      intros hptoq hnq hp,
      exact absurd (hptoq hp) hnq
    end


end chap3ex1

section chap3ex2
    open classical

    variables p q r s : Prop

    example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    begin
      intro h,
      cases (em p) with hp hnp,
      { cases (h hp) with hr hs,
        { left, exact (λ hp, hr) },
        right, exact (λ hp, hs)},
      left,
      intro hp,
      contradiction
    end

    example : ¬(p ∧ q) → ¬p ∨ ¬q :=
    begin
      intro h,
      cases (em p) with hp hnp,
      { cases (em q) with hq hnq,
        { exact (false.elim $ h ⟨hp, hq⟩) },
        right, exact hnq },
      left, exact hnp
    end

    example : ¬(p → q) → p ∧ ¬q :=
    begin
      intro h,
      cases (em p) with hp hnp,
      { cases (em q) with hq hnq,
        { have  ptoq : (p → q), from λ hp, hq,
          contradiction },
        constructor, assumption, assumption },
      cases (em q) with hq hnq,
      { have ptoq : p → q, from λ hp, absurd hp hnp,
        contradiction },
      have ptoq : p → q, { intro hp, contradiction },
      contradiction
    end

    example : (p → q) → (¬p ∨ q) :=
    begin
      intro h,
      cases (em p) with hp hnp,
      { right, exact h hp },
      left, exact hnp
    end

    example : (¬q → ¬p) → (p → q) :=
    begin
      intro h,
      cases (em q) with hq hnq,
        { exact (λ hp, hq) },
      have hnp : ¬p, from h hnq,
      exact (λ hp, absurd hp hnp)
    end

    example : p ∨ ¬p :=
    begin
      cases (em p) with hp hnp,
      { left, assumption },
      right, assumption
    end

    example : (((p → q) → p) → p) :=
    begin
      intro h,
      cases (em p) with hp hnp,
      { assumption },
      have ptoq : p → q, { intro hp, contradiction },
      exact h ptoq
    end

end chap3ex2

section chap3ex3

  example { p : Prop } : ¬(p ↔ ¬p) :=
  begin
    intro h,
    have nptop : ¬p → p, from iff.elim_right h,
    have ptonp : p → ¬p, from iff.elim_left h,
    have np : ¬p, { intro hp, exact absurd hp (ptonp hp) },
    exact absurd (nptop np) np
  end

end chap3ex3

section chap4ex1

  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  begin
    apply iff.intro,
    { intro h,
      constructor,
      repeat {
        intro ha,
        let h1 := h ha,
        exact h1.left <|> exact h1.right
      }},
    intros h ha,
    constructor,
    { exact h.left ha },
    exact h.right ha
  end

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  begin
    intros h1 h2 hx,
    exact (h1 hx $ h2 hx)
  end

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  begin
    intros h1 hx,
    cases h1 with hpx hqx,
    { left, exact hpx hx },
    right, exact hqx hx
  end

end chap4ex1

section chap4ex2

  variables (α : Type) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
  begin
    intro ha,
    apply iff.intro,
    { intro hr, exact hr ha },
    intros hr hx,
    assumption
  end

  -- one branch requires classical logic
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  begin
    apply iff.intro,
    { intros h,
      cases (classical.em r) with hr hnr,
      { right, assumption },
      left,
      intro hx,
      cases (h hx), assumption, contradiction },
    intros h hx,
    cases h with hpx hr,
    { left, exact hpx hx },
    right, exact hr
  end

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  begin
    apply iff.intro,
    { intros h hr hx, exact h hx hr },
    intros h hx hr, exact (h hr) hx
  end

end chap4ex2