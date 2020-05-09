
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

section chap4ex3

  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  begin
    have barber_case : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
    have barber_doesnt_shave_himself: ¬(shaves barber barber),
      begin
        intro h1,
        have : ¬ shaves barber barber, from (iff.elim_left barber_case) h1,
        contradiction
      end,
    have does_he_though : shaves barber barber, from (iff.elim_right barber_case) barber_doesnt_shave_himself,
    contradiction
  end

end chap4ex3

-- chap4ex4 doesn't involve any proof

section chap4ex5

  open classical

  variables (α : Type) (p q : α → Prop)
  variable a : α
  variable r : Prop

  include a

  example : (∃ x : α, r) → r :=
  begin
    intro h,
    cases h,
    assumption
  end

  example : r → (∃ x : α, r) :=
  begin
    intro h,
    constructor, exact a, exact h
  end


  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  begin
    apply iff.intro,
    { intro h,
      cases h with ha hconj,
      constructor,
      { existsi ha, exact hconj.left },
      exact hconj.right },
    intro h,
    have ex : ∃ x, p x, from h.left,
    cases ex with hx hpx,
    existsi hx,
    constructor,
    { exact hpx },
    exact h.right,
  end

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  begin
    apply iff.intro,
    { intro h,
      cases h with hx hdisj,
      cases hdisj with hpx hqx,
      { left, existsi hx, exact hpx },
      right, existsi hx, exact hqx },
    intro h,
    cases h with hpx hqx,
    { cases hpx with hx hpx', existsi hx, left, exact hpx' },
    cases hqx with hx hqx', existsi hx, right, exact hqx'
  end

  def forall_px_not_exists_not_px : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  begin
    apply iff.intro,
    { intros h hcon,
      cases hcon with hx hnpx,
      have hpx : p hx, from h hx,
      contradiction },
    intros h hx,
    cases (classical.em (p hx)) with _ hnpx,
    { show p hx, by assumption },
    show p hx,
    have : ∃ x, ¬p x, { existsi hx, exact hnpx },
    contradiction
  end

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := @forall_px_not_exists_not_px α p a

  def exists_p_x_not_forall_not_px : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  begin
    apply iff.intro,
    { intros h hcon,
      cases h with hx hpx,
      have hnpx : ¬ p hx, { exact hcon hx },
      contradiction },
    show ¬(∀ x, ¬p x) → (∃ x, p x),
    intro h,
    cases (classical.em (∃ x, p x)) with _ hnex,
    { assumption },
    have hcont : ∀x, ¬p x, {
        intros hx hpx,
        have hex : ∃ x, p x, { existsi hx, exact hpx },
        contradiction
      },
    contradiction
  end

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := @exists_p_x_not_forall_not_px α p a

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  begin
    apply iff.intro,
    { intros h hx,
      cases (em (p hx)) with hpx hnpx,
      { have : ∃ x, p x, from ⟨hx, hpx⟩,
        contradiction },
      assumption },
    intros h hcont,
    cases hcont with hx hpx,
    have nphx : ¬ p hx, from h hx,
    contradiction
  end

  def not_forall_exists_not_equivalence : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  begin
    apply iff.intro,
    { intro h,
      cases (em (p a)) with hpa hnpa,
      { cases (em ∃ x, ¬ p x) with hexists hnexists,
        { assumption },
        have : ∀ x, p x, from iff.elim_right (@forall_px_not_exists_not_px α p a) hnexists,
        contradiction },
      existsi a, exact hnpa },
    intros h hcont,
    cases h with hx hnpx,
    have hpx : p hx, from hcont hx,
    contradiction
  end

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := @not_forall_exists_not_equivalence α p a

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  begin
    apply iff.intro,
    { intros h hex,
      cases hex with hx hpx,
      exact h hx hpx},
    intros h hx hphx,
    have : ∃ x, p x, from ⟨hx, hphx⟩,
    exact h this
  end

  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  begin
    apply iff.intro,
    { intros hex hfa,
      cases hex with hx hphx,
      have hhx : p hx, from hfa hx,
      exact hphx hhx },
    intros h,
    cases (em (∀ (x : α), p x)) with hyes hno,
    { existsi a, intro hpa, exact h hyes },
    have : (∃ x, ¬ p x), from iff.elim_left (@not_forall_exists_not_equivalence α p a) hno,
    cases this with hx hnpx,
    existsi hx, intro hpx, contradiction
  end

  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  begin
    apply iff.intro,
    { intros hex hr,
      cases hex with hx hrtopx,
      existsi hx, exact hrtopx hr },
    intro h,
    cases (em r) with hr hnr,
    { have : (∃ (x : α), p x), from h hr,
      cases this with hx hpx,
      existsi hx, intro hr, exact hpx },
    existsi a, intro hr, contradiction
  end

end chap4ex5

section chap4ex6
  variables (real : Type) [ordered_ring real]
  variables (log exp : real → real)
  variable  log_exp_eq : ∀ x, log (exp x) = x
  variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
  variable  exp_pos    : ∀ x, exp x > 0
  variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

  -- this ensures the assumptions are available in tactic proofs
  include log_exp_eq exp_log_eq exp_pos exp_add

  example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

  example (y : real) (h : y > 0)  : exp (log y) = y :=
  exp_log_eq h

  theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
  let x := x, y := y in
  begin
    have s1 : log (x * y) = log (x * y), by reflexivity,
    have s2 : log (x * y) = log (exp (log x) * (exp (log y))), by { rw (exp_log_eq hx), rw (exp_log_eq hy) },
    have s3 : log (exp (log x) * (exp (log y))) = log (exp (log x + log y)), by { rw exp_add },
    have s4 : log (exp (log x + log y)) = log x + log y, by rw log_exp_eq,
    show log (x * y) = log x + log y, by rw [s1, s2, s3, s4],
  end

end chap4ex6

section chap4ex7

  #check sub_self

  example (x : ℤ) : x * 0 = 0 :=
  calc
    x * 0 = 0 * x : by rw [mul_comm]
      ... = (x - x) * x : by rw sub_self
      ... = (x * x) - (x * x) : by rw sub_mul
      ... = 0 : by rw sub_self

end chap4ex7
