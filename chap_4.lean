
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

namespace ex3

    variables (men : Type) (barber : men)
    variable  (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    have h1 : shaves barber barber → ¬ shaves barber barber, from iff.elim_left $ h barber,
    have h2 : ¬ shaves barber barber → shaves barber barber, from iff.elim_right $ h barber,
    have nsbb : ¬shaves barber barber, from λ hsbb : shaves barber barber, absurd hsbb (h1 hsbb),
    have sbb : shaves barber barber, from h2 nsbb,
    absurd sbb nsbb

end ex3

namespace ex4
    namespace hidden

        def divides (m n : ℕ) : Prop := ∃ k, m * k = n

        instance : has_dvd nat := ⟨divides⟩

        def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

        section
            variables m n : ℕ

            #check m ∣ n
            #check m^n
            #check even (m^n + 3)
        end

    end hidden

    def prime (n : ℕ) : Prop := n > 1 ∧ ¬   (∃ m : ℕ, m < n ∧ hidden.divides m n)

    def infinitely_many_primes : Prop := ∀ n : ℕ,
        prime n ∧ (∃ m : ℕ, prime m ∧ n < m)
        ∨ ¬(prime n)

    def Fermat_prime (n : ℕ) : Prop := prime n ∧ n > 2 ∧ (∃ k : ℕ , (2^k + 1) = n)

    def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ,
        (Fermat_prime n ∧ (∃ m : ℕ, Fermat_prime m ∧ m > n))
        ∨ ¬(Fermat_prime n)

    def goldbach_conjecture : Prop := ∀ n : ℕ,
    n < 2
    ∨ ¬(hidden.even n)
    ∨ ∃ a b : ℕ, prime a ∧ prime b ∧ (a + b = n)

    -- Every odd number greater than 5 can be expressed as the sum of three primes. (A prime may be used more than once in the same sum.)
    -- https://en.wikipedia.org/wiki/Goldbach%27s_weak_conjecture
    def Goldbach's_weak_conjecture : Prop := ∀ n : ℕ,
    n < 5
    ∨ hidden.even n
    ∨ (∃ a b c : ℕ, prime a ∧ prime b ∧ prime c ∧ a + b + c = n )

    def Fermat's_last_theorem : Prop := ∀ n : ℕ,
    n ≤ 2
    ∨ ¬(∃ a b c : ℕ, a^n + b^n = c^n)

end ex4

namespace ex5
    open classical

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    def pikachu (h : ∃ x : α, r) : r :=
    match h with ⟨hx, hr⟩ := hr end

    def raichu (hr : r) : (∃ x : α, r) := exists.intro a hr

    def pichu : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    have left : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r, from
        assume h : (∃ x, p x ∧ r),
        match h with ⟨hx, h1⟩ :=
            and.intro (⟨hx, h1.left⟩) h1.right
        end,
    have right : (∃ x, p x) ∧ r → (∃ x, p x ∧ r), from
        assume h,
        match h.left with ⟨hx, hpx⟩ :=
            ⟨hx, and.intro hpx h.right⟩
        end,
    ⟨left, right⟩

    def jesse : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    have left : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x),from
        assume ⟨hx, h1⟩,
        or.elim h1 (λ hpx, or.inl ⟨hx, hpx⟩) (λ hqx, or.inr ⟨hx, hqx⟩),
    have right : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x), from
        assume h,
        or.elim h (λ ⟨hx, hpx⟩, ⟨hx, or.inl hpx⟩) (λ ⟨hx, hqx⟩, ⟨hx, or.inr hqx⟩),
    ⟨left, right⟩

    -- May require classical reasoning
    def james : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    have left : (∀ x, p x) → ¬ (∃ x, ¬ p x), from
        assume h1,
        assume h2 : (∃ x, ¬ p x),
        have ¬ (∀ x, p x), from
            match h2 with ⟨hx, hnpx⟩ :=
                absurd (h1 hx) hnpx
            end,
        absurd h1 this,
    have right : ¬ (∃ x, ¬ p x) → (∀ x, p x), from
        assume h1,
        λ hx, by_contradiction (λ hnpx, h1 ⟨hx, hnpx⟩),
    ⟨left, right⟩

    theorem dne {p : Prop} (h : ¬¬p) : p :=
    or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)


    def team_rocket : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    have left : (∃ x, p x) → ¬ (∀ x, ¬ p x), from
        assume h1 h2,
        match h1 with ⟨hx, hpx⟩ :=
            absurd hpx (h2 hx)
        end,
    have right : ¬ (∀ x, ¬ p x) → (∃ x, p x), from
        assume h,
        by_contradiction (
            λ hnex,
            have (∀ x, ¬ p x), from (
                λ x, by_contradiction (λ h2, absurd (⟨x, dne h2⟩ : (∃ x, p x)) hnex)
            ),
            absurd this h
        ),
    ⟨left, right⟩

    def prepare_for_trouble : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    have left : (¬ ∃ x, p x) → (∀ x, ¬ p x), from (
        assume hne,
        λ x, by_cases (λ (hpx : p x), absurd (⟨x, hpx⟩ : ∃ x, p x) hne) (λ hnpx, hnpx)
    ),
    have right : (∀ x, ¬ p x) → (¬ ∃ x, p x), from
        assume h1 h2,
        match h2 with ⟨hx, hpx⟩ := absurd hpx (h1 hx) end,
    ⟨left, right⟩

    def make_it_double : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    have left : ¬(∀ x, p x) → (∃ x, ¬ p x), from
        assume h,
        by_contradiction (
            λ hnex,
            have (∀ x, p x), from (
                λ hx, or.elim (em $p hx)
                    (λ hphx, hphx)
                    (λ hnphx, absurd (⟨hx, hnphx⟩ : ∃ x, ¬ p x) hnex)
            ),
            absurd this h
        ),
    have right : (∃ x, ¬ p x) → ¬(∀ x, p x), from
        assume h,
        match h with ⟨hx, hnpx⟩ :=
            λ h2, absurd (h2 hx) hnpx
        end,
    ⟨left, right⟩

    def to_protect_the_world : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    have left : (∀ x, p x → r) → (∃ x, p x) → r, from
        assume h hpx,
        match hpx with ⟨hx, hpx⟩ := h _ hpx end,
    have right : ((∃ x, p x) → r) → (∀ x, p x → r), from
        assume h,
        λ hx hpx, h $ ⟨hx, hpx⟩,
    ⟨left, right⟩

    -- See the book: we need the assumption that α is nonempty here (a)
    def from_devastation : (∃ x, p x → r) ↔ ((∀ x, p x) → r) :=
    have left : (∃ x, p x → r) → ((∀ x, p x) → r), from
        assume h1 h2,
            match h1 with ⟨hx, hpxtor⟩ :=
                hpxtor (h2 hx)
            end,
    have right : ((∀ x : α, p x) → r) → (∃ x : α, p x → r), from
        assume h,
            -- Had too look up that part from the book
            by_cases
                (λ hap : (∀ x : α, p x), ⟨a, λ _hleft, h hap⟩)
                (λ hnap : ¬(∀ x : α, p x),
                    by_contradiction (
                        λ hnex : ¬ ∃ x, p x → r,
                        have hap : ∀ x, p x, from (
                            assume x : α,
                            by_contradiction (
                                assume hnp : ¬ p x,
                                    have hex : ∃ x, p x → r,
                                    from ⟨x, (assume hp, absurd hp hnp)⟩,
                                    show false, from hnex hex
                            )
                        ),
                        show false, from hnap hap
                    )
                ),
    ⟨left, right⟩

    -- See the book: we need the assumption that α is nonempty here (a)
    def to_unite_all_peoples : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    have left : (∃ x, r → p x) → (r → ∃ x, p x), from
        assume h hr,
        match h with ⟨hx, hrpx⟩ :=
            ⟨hx, hrpx hr⟩
        end,
    have right : (r → ∃ x, p x) → (∃ x, r → p x), from
        assume h,
        by_contradiction (
            λ (hnex : ¬∃ x, r → p x),
            have hx : α, from a,
            have h1 : ∀ x, ¬(r → p x), from λ hx h2, hnex ⟨hx, h2⟩,
            have h2 : ¬∃ x, p x, from (
                assume hn : ∃ x, p x,
                match hn with ⟨hx, hpx⟩ :=
                    absurd (λ hr, hpx) (h1 hx)
                end
            ),
            have h3 : r → ¬∃ x, p x, from λ hr, h2,
            have h4 : r → ∀ x, ¬ p x, from λ hr, forall_not_of_not_exists $ h3 hr,
            have ¬(r → ∃ x, p x), from (
                assume h,
                or.elim (em r)
                    (λ hr,
                    absurd (h hr) (h3 hr)
                    )
                    (λ hnr,
                    have ∃ x, r → p x, from ⟨hx, λ hr, absurd hr hnr⟩,
                    show false, from absurd this hnex
                    )
            ),
            show false, from absurd h this
        ),
    ⟨left, right⟩

    -- =============
    -- === Goals ===
    -- =============

    example : (∃ x : α, r) → r := pikachu α r
    example : r → (∃ x : α, r) := raichu α a r
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := pichu α p r
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := jesse α p q

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := james α p
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := team_rocket α p
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := prepare_for_trouble α p
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := make_it_double α p

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := to_protect_the_world α p r
    -- See the book: we need the assumption that α is nonempty here (a)
    example : (∃ x, p x → r) ↔ (∀ x, p x) → r := from_devastation α p a r
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := to_unite_all_peoples α p a r

end ex5
