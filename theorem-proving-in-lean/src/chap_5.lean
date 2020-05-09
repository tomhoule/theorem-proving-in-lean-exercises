
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
