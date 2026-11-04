# 值判据 (四): `Lv` 上的规格与不动点行

> **判决: PARTIAL (`FixRow` 条件于切口与链点规格).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). 载体是 [InaccTreeBase](InaccTreeBase.lagda.md) 的 `Ordᴸ`, 规格 `IsPsiᴸ` 是 [OCFSpecLv](OCFSpecLv.lagda.md) 的陈述. 这里补上它的性质 (`irr`, 唯一, $t\notin C$) 和**不动点行** `FixRow`: 对字面的 $\Omega_\Omega$, $\Omega_{\Omega\cdot2}$ 这样的 $A$, 只要 (1) $a_n$ 上升且在 $A$ 以下, (2) $t_n$ 是 $\psi_0(a_n)$, (3) 切口 `Cut`: $C_0(a_n)$ 里低于 $A$ 的成员低于 $a_{n+1}$, 就有 $\psi_0(A)=\sup t_n$. 没有判决, 没有替身, 不要 `ΩO`.
>
> `Cut` 是条件. 对 $A=\Omega_\Omega$ 由三条层号的性质推出 (`cut-ΩΩ`). 这三条是关于 `Lv` 的值序的陈述, 见 §3.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeSpec where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv; Sim; add)
open import OCF.Align.OCFSpecLv
  using (_≼ᴸ_; _≺ᴸ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼ᴸ-trans; Accᴸ; acc; acc-≼ᴸ; wfᴸ; belowᴸ; rf; ρ;
         Clᴸ₊; base; plus; col; cg; Witᴸ; wit; Supᴸ; sup; IsPsiᴸₐ; IsPsiᴸ; LΩ)
```

## §1 值序与规格的性质

```agda
≼ᴸ-refl : ∀ {ℓ} (a : Ordᴸ ℓ) → a ≼ᴸ a
≼ᴸ-refl Tree.zero    = z≼
≼ᴸ-refl (Tree.suc a) = s≼s (≼ᴸ-refl a)
≼ᴸ-refl (Tree.lim f) = l≼ (λ n → ≼l n (≼ᴸ-refl (f n)))
≼ᴸ-refl {ℓ} (limᵢ r f) = i≼ (λ x → ≼i x (≼ᴸ-refl (f (intoL ℓ r x))))
≼ᴸ-refl {suc k}    (up d y) = u≼ (≼u (≼ᴸ-refl y))
≼ᴸ-refl {lim f}    (up d y) = u≼ (≼u (≼ᴸ-refl y))
≼ᴸ-refl {limᴼ k g} (up d y) = u≼ (≼u (≼ᴸ-refl y))

≼ᴸ-suc : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} → a ≼ᴸ b → a ≼ᴸ Tree.suc b
≼ᴸ-suc z≼       = z≼
≼ᴸ-suc (s≼s p)  = s≼s (≼ᴸ-suc p)
≼ᴸ-suc (≼l {f = f} n p)  = ≼ᴸ-trans (≼ᴸ-suc p) (s≼s (≼l n (≼ᴸ-refl (f n))))
≼ᴸ-suc (l≼ p)   = l≼ (λ n → ≼ᴸ-suc (p n))
≼ᴸ-suc {ℓ₂ = ℓ₂} (≼i {r = r} {f = f} x p) = ≼ᴸ-trans (≼ᴸ-suc p) (s≼s (≼i x (≼ᴸ-refl (f (intoL ℓ₂ r x)))))
≼ᴸ-suc (i≼ p)   = i≼ (λ x → ≼ᴸ-suc (p x))
≼ᴸ-suc {ℓ₂ = ℓ₂} (≼u {d = d} {y = y} p) = ≼ᴸ-trans (≼ᴸ-suc p) (s≼s (≼u (≼ᴸ-refl (outD ℓ₂ d y))))
≼ᴸ-suc (u≼ p)   = u≼ (≼ᴸ-suc p)

≺→≼ᴸ : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} → a ≺ᴸ b → a ≼ᴸ b
≺→≼ᴸ {a = a} p = ≼ᴸ-trans (≼ᴸ-suc (≼ᴸ-refl a)) p

≺ᴸ-irrefl : ∀ {k} (a : Ordᴸ k) → ¬ (a ≺ᴸ a)
≺ᴸ-irrefl a = go (wfᴸ a) where
  go : ∀ {k} {a : Ordᴸ k} → Accᴸ a → ¬ (a ≺ᴸ a)
  go {a = a} (acc h) q = go (h a q) q

below→≼ᴸ : ∀ {n n′} (t : Ordᴸ n) {t′ : Ordᴸ n′} → (∀ {m} {y : Ordᴸ m} → y ≺ᴸ t → y ≺ᴸ t′) → t ≼ᴸ t′
below→≼ᴸ Tree.zero h = z≼
below→≼ᴸ (Tree.suc c) h = h (≼ᴸ-refl (Tree.suc c))
below→≼ᴸ (Tree.lim g) h = l≼ (λ n → below→≼ᴸ (g n) (λ q → h (≼l n q)))
below→≼ᴸ {n} (limᵢ r g) h = i≼ (λ x → below→≼ᴸ (g (intoL n r x)) (λ q → h (≼i x q)))
below→≼ᴸ {suc k}    (up d y) h = u≼ (below→≼ᴸ y (λ q → h (≼u q)))
below→≼ᴸ {lim f}    (up d y) h = u≼ (below→≼ᴸ y (λ q → h (≼u q)))
below→≼ᴸ {limᴼ k g} (up d y) h = u≼ (below→≼ᴸ y (λ q → h (≼u q)))

Recᴸ : ∀ {k} (a : Ordᴸ k) → Accᴸ a → (u : Lv) → ∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a → ∀ {n} → Ordᴸ n → Set
Recᴸ a (acc h) u ξ q x = IsPsiᴸₐ u ξ (h ξ q) x

Cᴸₐ : (v : Lv) → ∀ {k} (a : Ordᴸ k) → Accᴸ a → ∀ {m} → Ordᴸ m → Set
Cᴸₐ v a ac = Clᴸ₊ v a (Recᴸ a ac)

Cᴸ : (v : Lv) → ∀ {k} (a : Ordᴸ k) → ∀ {m} → Ordᴸ m → Set
Cᴸ v a = Cᴸₐ v a (wfᴸ a)

Cl-map : ∀ {v v′ k k′} {a : Ordᴸ k} {a′ : Ordᴸ k′}
         {R : (u : Lv) → ∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a → ∀ {n} → Ordᴸ n → Set}
         {R′ : (u : Lv) → ∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a′ → ∀ {n} → Ordᴸ n → Set} →
         Ω v ≼ᴸ Ω v′ → (ea : a ≼ᴸ a′) →
         (∀ u {m} (ξ : Ordᴸ m) (q : ξ ≺ᴸ a) {n} (x : Ordᴸ n) → R u ξ q x → R′ u ξ (≼ᴸ-trans q ea) x) →
         ∀ {m} {x : Ordᴸ m} → Clᴸ₊ v a R x → Clᴸ₊ v′ a′ R′ x
Cl-map ev ea rr (base q)        = base (≼ᴸ-trans q ev)
Cl-map ev ea rr (plus σ c d)    = plus σ (Cl-map ev ea rr c) (Cl-map ev ea rr d)
Cl-map ev ea rr (col cu cξ q r) = col (Cl-map ev ea rr cu) (Cl-map ev ea rr cξ) (≼ᴸ-trans q ea) (rr _ _ q _ r)
Cl-map ev ea rr (cg e e′ c)     = cg e e′ (Cl-map ev ea rr c)

Sup-map : ∀ {v} {S S′ : ∀ {m} → Ordᴸ m → Set} {n} {t : Ordᴸ n} →
          (∀ {m} {x : Ordᴸ m} → S x → S′ x) → (∀ {m} {x : Ordᴸ m} → S′ x → S x) → Supᴸ v S t → Supᴸ v S′ t
Sup-map f g (sup l u c) = sup l (λ s b → u (g s) b) (λ q → let w = c q in wit (f (Witᴸ.mem w)) (Witᴸ.bd w) (Witᴸ.dom w))

irr : ∀ {v k k′} {a : Ordᴸ k} {a′ : Ordᴸ k′} (ac : Accᴸ a) (ac′ : Accᴸ a′) → a ≼ᴸ a′ → a′ ≼ᴸ a →
      ∀ {n} {t : Ordᴸ n} → IsPsiᴸₐ v a ac t → IsPsiᴸₐ v a′ ac′ t
irr {a = a} {a′ = a′} (acc h) (acc h′) e e′ =
  Sup-map (Cl-map (≼ᴸ-refl _) e  (λ u ξ q x r → irr (h ξ q) (h′ ξ (≼ᴸ-trans q e))  (≼ᴸ-refl ξ) (≼ᴸ-refl ξ) r))
          (Cl-map (≼ᴸ-refl _) e′ (λ u ξ q x r → irr (h′ ξ q) (h ξ (≼ᴸ-trans q e′)) (≼ᴸ-refl ξ) (≼ᴸ-refl ξ) r))

Cₐ-map : ∀ {v k k′} {a : Ordᴸ k} {a′ : Ordᴸ k′} (ac : Accᴸ a) (ac′ : Accᴸ a′) → a ≼ᴸ a′ →
         ∀ {m} {x : Ordᴸ m} → Cᴸₐ v a ac x → Cᴸₐ v a′ ac′ x
Cₐ-map (acc h) (acc h′) e = Cl-map (≼ᴸ-refl _) e (λ u ξ q x r → irr (h ξ q) (h′ ξ (≼ᴸ-trans q e)) (≼ᴸ-refl ξ) (≼ᴸ-refl ξ) r)

C-mono : ∀ {v k k′} {a : Ordᴸ k} {a′ : Ordᴸ k′} → a ≼ᴸ a′ → ∀ {m} {x : Ordᴸ m} → Cᴸ v a x → Cᴸ v a′ x
C-mono {a = a} {a′ = a′} = Cₐ-map (wfᴸ a) (wfᴸ a′)

Sup-≼ : ∀ {v v′} {S S′ : ∀ {m} → Ordᴸ m → Set} {n n′} {t : Ordᴸ n} {t′ : Ordᴸ n′} →
        (∀ {m} {x : Ordᴸ m} → S x → S′ x) → (∀ {m} {x : Ordᴸ m} → S x → x ≺ᴸ Ω (suc v) → x ≺ᴸ Ω (suc v′)) →
        Supᴸ v S t → Supᴸ v′ S′ t′ → t ≼ᴸ t′
Sup-≼ {t = t} f b s s′ = below→≼ᴸ t (λ q →
  let w = Supᴸ.cof s q in ≼ᴸ-trans (s≼s (Witᴸ.dom w)) (Supᴸ.ub s′ (f (Witᴸ.mem w)) (b (Witᴸ.mem w) (Witᴸ.bd w))))

IsPsiᴸ-mono : ∀ {v k k′} {a : Ordᴸ k} {a′ : Ordᴸ k′} → a ≼ᴸ a′ → ∀ {n n′} {t : Ordᴸ n} {t′ : Ordᴸ n′} →
              IsPsiᴸ v a t → IsPsiᴸ v a′ t′ → t ≼ᴸ t′
IsPsiᴸ-mono {a = a} {a′ = a′} e = Sup-≼ (Cₐ-map (wfᴸ a) (wfᴸ a′) e) (λ _ b → b)

IsPsiᴸ-uniq : ∀ {v k} {a : Ordᴸ k} {n n′} {t : Ordᴸ n} {t′ : Ordᴸ n′} → IsPsiᴸ v a t → IsPsiᴸ v a t′ → t ≼ᴸ t′
IsPsiᴸ-uniq {a = a} = IsPsiᴸ-mono (≼ᴸ-refl a)

Sup-t : ∀ {v} {S : ∀ {m} → Ordᴸ m → Set} {n n′} {t : Ordᴸ n} {t′ : Ordᴸ n′} → t ≼ᴸ t′ → t′ ≼ᴸ t → Supᴸ v S t → Supᴸ v S t′
Sup-t e e′ (sup l u c) = sup (≼ᴸ-trans (s≼s e′) l) (λ s b → ≼ᴸ-trans (u s b) e) (λ q → c (≼ᴸ-trans q e′))

¬inᴸ : ∀ {v k} {a : Ordᴸ k} {n} {t : Ordᴸ n} → IsPsiᴸ v a t → ¬ (Cᴸ v a t)
¬inᴸ {t = t} s c = ≺ᴸ-irrefl t (Supᴸ.ub s c (Supᴸ.lt s))

Ω-floorᴸ : ∀ {u k n} {ξ : Ordᴸ k} {w : Ordᴸ n} (ac : Accᴸ ξ) → IsPsiᴸₐ u ξ ac w → Ω u ≼ᴸ w
Ω-floorᴸ {u} (acc h) r = below→≼ᴸ (Ω u) (λ q → Supᴸ.ub r (base q) (≼ᴸ-trans q (Ω≼Ω⁺ u)))
  where
  Ω≼Ω⁺ : ∀ v → Ω v ≼ᴸ Ω (suc v)
  Ω≼Ω⁺ v = ≺→≼ᴸ {a = Ω v} (≼i (Tree.suc (Ω v)) (≼u (≼ᴸ-refl (Tree.suc (Ω v)))))
```

## §2 不动点行

```agda
module FixRow {lv : ℕ → Lv} (a : (i : ℕ) → Ordᴸ (lv i)) {K} (A : Ordᴸ K) (t : ℕ → Ordᴸ zero)
              (H   : ∀ n → IsPsiᴸ zero (a n) (t n))
              (stp : ∀ n → a n ≼ᴸ a (suc n))
              (a≼A : ∀ n → a n ≼ᴸ A)
              (Cut : ∀ n {m} {y : Ordᴸ m} → Cᴸ zero (a n) y → y ≺ᴸ A → y ≺ᴸ a (suc n)) where

  a-add : ∀ k n → a n ≼ᴸ a (k +ᴺ n)
  a-add zero    n = ≼ᴸ-refl (a n)
  a-add (suc k) n = ≼ᴸ-trans (a-add k n) (stp (k +ᴺ n))

  aˡ : ∀ n k → a n ≼ᴸ a (n +ᴺ k)
  aˡ n k = subst (λ w → a n ≼ᴸ a w) (+-comm k n) (a-add k n)

  C↑ : ∀ {n n′} → a n ≼ᴸ a n′ → ∀ {m} {x : Ordᴸ m} → Cᴸ zero (a n) x → Cᴸ zero (a n′) x
  C↑ = C-mono

  irrR : ∀ {N′ u m n} {ξ : Ordᴸ m} {x′ : Ordᴸ n} (q₁ : ξ ≺ᴸ A) (q₂ : ξ ≺ᴸ a N′) → Recᴸ A (wfᴸ A) u ξ q₁ x′ → Recᴸ (a N′) (wfᴸ (a N′)) u ξ q₂ x′
  irrR {N′} {ξ = ξ} q₁ q₂ r′ = irr (belowᴸ A ξ q₁) (belowᴸ (a N′) ξ q₂) (≼ᴸ-refl ξ) (≼ᴸ-refl ξ) r′

  -- 括号: C₀(A) 落在某个 C₀(aₙ) 里
  br : ∀ {m} {x : Ordᴸ m} → Clᴸ₊ zero A (Recᴸ A (wfᴸ A)) x → Σ ℕ λ n → Cᴸ zero (a n) x
  br (base q) = 0 , base q
  br (plus σ c d) with br c | br d
  ... | n₁ , c₁ | n₂ , c₂ = (n₁ +ᴺ n₂) , plus σ (C↑ (aˡ n₁ n₂) c₁) (C↑ (a-add n₁ n₂) c₂)
  br (cg e e′ c) with br c
  ... | n , c₁ = n , cg e e′ c₁
  br (col {u} {ξ = ξ} cu cξ q r) with br cu | br cξ
  ... | n₁ , c₁ | n₂ , c₂ =
    let N  = n₁ +ᴺ n₂
        cu′ = C↑ (aˡ n₁ n₂) c₁
        cξ′ = C↑ (a-add n₁ n₂) c₂
        q′ = Cut N cξ′ q
    in suc N , col (C↑ (stp N) cu′) (C↑ (stp N) cξ′) q′ (irrR {N′ = suc N} q q′ r)

  fix : IsPsiᴸ zero A (Tree.lim t)
  fix = sup
    (≼i (Tree.suc (Tree.lim t)) (≼u (≼ᴸ-refl (Tree.suc (Tree.lim t)))))
    (λ c b → let n , c′ = br c in ≼l n (Supᴸ.ub (H n) c′ b))
    (λ { (≼l n q) → let w = Supᴸ.cof (H n) q in wit (C-mono (a≼A n) (Witᴸ.mem w)) (Witᴸ.bd w) (Witᴸ.dom w) })
```

## §3 $\Omega_\Omega$ 的切口

**条件.** 下面三条是关于层号的值序的陈述. 经典地都成立 (判断): `Lv` 上 $\Omega_u$ 由 $u$ 的值决定, 严格递增, 且 $\Omega_{\ell}$ 对加法封闭. 没有证, 第一个困难是 `ΩRefl`: $\Omega_u\prec\Omega_{\mathrm{lv}\,x}$ 推 $u\prec x$ 要从第 $\mathrm{lv}\,x$ 层的树里读出 $u$ 的后继, 而 $u$ 与 $\mathrm{lv}\,x$ 没有字面的路径 (见 `no-lim-cmp`, `no-join` 的同类现象; 这里只是证不出, 没有否定). 文件 [OCFSpecRule](OCFSpecRule.lagda.md) 的 `ΩO` 是它的非严格版本, 那里也只证了 $v=0,1$.

```agda
rf-≼ : ∀ (x : Ordᴸ zero) → rf (toLv x) ≼ᴸ x
rf-≼ Tree.zero    = z≼
rf-≼ (Tree.suc x) = s≼s (rf-≼ x)
rf-≼ (Tree.lim f) = l≼ (λ n → u≼ (≼l n (rf-≼ (f n))))

𝟏ᴸ : Ordᴸ zero
𝟏ᴸ = Tree.suc Tree.zero

1≼Ω : ∀ v → 𝟏ᴸ ≼ᴸ Ω v
1≼Ω zero       = s≼s z≼
1≼Ω (suc v)    = ≼i (Tree.suc Tree.zero) (≼u (s≼s z≼))
1≼Ω (lim f)    = ≼l 0 (≼u (1≼Ω (f 0)))
1≼Ω (limᴼ k g) = ≼i Tree.zero (≼u (1≼Ω (g Tree.zero)))

out-intoL : ∀ ℓ r (x : Ordᴸ (at ℓ r)) → outL ℓ r (intoL ℓ r x) ≡ x
out-intoL (suc k)    (inj₁ _)        y = refl
out-intoL (suc k)    (inj₂ r)        y = out-intoL k r y
out-intoL (lim f)    (n , r)         y = out-intoL (f n) r y
out-intoL (limᴼ k g) (inj₁ (inj₁ _)) y = refl
out-intoL (limᴼ k g) (inj₁ (inj₂ r)) y = out-intoL k r y
out-intoL (limᴼ k g) (inj₂ (x , r))  y = out-intoL (g x) r y

add-≽ˡ : ∀ {k ℓ} (a : Ordᴸ ℓ) (σ : Sim k ℓ) (b : Ordᴸ k) → a ≼ᴸ add a σ b
add-≽ˡ a σ Tree.zero    = ≼ᴸ-refl a
add-≽ˡ a σ (Tree.suc b) = ≼ᴸ-suc (add-≽ˡ a σ b)
add-≽ˡ a σ (Tree.lim f) = ≼l 0 (add-≽ˡ a σ (f 0))
add-≽ˡ {k} a σ (limᵢ r f) = ≼i Tree.zero (add-≽ˡ a σ _)
add-≽ˡ {suc k}    a σ (up d x) = add-≽ˡ a _ x
add-≽ˡ {lim f}    a σ (up d x) = add-≽ˡ a _ x
add-≽ˡ {limᴼ k g} a σ (up d x) = add-≽ˡ a _ x

subst-sym : ∀ {A : Set} (P : A → Set) {x y : A} (e : x ≡ y) (z : P y) → subst P e (subst P (sym e) z) ≡ z
subst-sym P refl z = refl

add-≽ʳ : ∀ {k ℓ} (a : Ordᴸ ℓ) (σ : Sim k ℓ) (b : Ordᴸ k) → b ≼ᴸ add a σ b
add-≽ʳ a σ Tree.zero    = z≼
add-≽ʳ a σ (Tree.suc b) = s≼s (add-≽ʳ a σ b)
add-≽ʳ a σ (Tree.lim f) = l≼ (λ n → ≼l n (add-≽ʳ a σ (f n)))
add-≽ʳ {k} {ℓ} a σ (limᵢ r f) = i≼ (λ x →
  let r′ = proj₁ (σ r) ; e = proj₂ (σ r) ; x′ = subst Ordᴸ (sym e) x
      eq : subst Ordᴸ e (outL ℓ r′ (intoL ℓ r′ x′)) ≡ x
      eq = aux e (out-intoL ℓ r′ x′) (subst-sym Ordᴸ e x)
  in ≼i x′ (subst (λ w → f (intoL k r x) ≼ᴸ add a σ (f (intoL k r w))) (sym eq) (add-≽ʳ a σ (f (intoL k r x)))))
  where
  aux : ∀ {u v : Lv} (e : u ≡ v) {w w′ : Ordᴸ u} {x : Ordᴸ v} → w ≡ w′ → subst Ordᴸ e w′ ≡ x → subst Ordᴸ e w ≡ x
  aux e refl p = p
add-≽ʳ {suc k}    a σ (up d x) = u≼ (add-≽ʳ a _ x)
add-≽ʳ {lim f}    a σ (up d x) = u≼ (add-≽ʳ a _ x)
add-≽ʳ {limᴼ k g} a σ (up d x) = u≼ (add-≽ʳ a _ x)

ltₐ : ∀ {v k n} {a : Ordᴸ k} {t : Ordᴸ n} (ac : Accᴸ a) → IsPsiᴸₐ v a ac t → t ≺ᴸ Ω (suc v)
ltₐ (acc h) s = Supᴸ.lt s

module CutΩΩ (x : ℕ → Ordᴸ zero) (t : ℕ → Ordᴸ zero)
             (H   : ∀ n → IsPsiᴸ zero (Ω (toLv (x n))) (t n))
             (stx : ∀ n → x n ≺ᴸ t n)
             -- 条件 (经典地成立, 判断)
             (ΩRefl : ∀ u → Ω u ≺ᴸ Ω LΩ → rf u ≺ᴸ Ω (suc zero))
             (ΩStep : ∀ n u → rf u ≺ᴸ t n → Ω (suc u) ≼ᴸ Ω (toLv (x (suc n))))
             (ΩPrin : ∀ n {m k} {y : Ordᴸ m} {z : Ordᴸ k} (σ : Sim k m) → y ≺ᴸ Ω (toLv (x n)) → z ≺ᴸ Ω (toLv (x n)) → add y σ z ≺ᴸ Ω (toLv (x n))) where

  a : (n : ℕ) → Ordᴸ (toLv (x n))
  a n = Ω (toLv (x n))

  A : Ordᴸ LΩ
  A = Ω LΩ

  a≼A : ∀ n → a n ≼ᴸ A
  a≼A n = ≼i (x n) (≼u (≼ᴸ-refl (a n)))

  a≺a : ∀ n → a n ≼ᴸ a (suc n)
  a≺a n = ≼ᴸ-trans (≼i (Tree.suc (Ω (toLv (x n)))) (≼u (≼ᴸ-suc (≼ᴸ-refl (Ω (toLv (x n)))))))
                   (ΩStep n (toLv (x n)) (≼ᴸ-trans (s≼s (rf-≼ (x n))) (stx n)))

  go : ∀ n {m} {y : Ordᴸ m} → Clᴸ₊ zero (a n) (Recᴸ (a n) (wfᴸ (a n))) y → y ≺ᴸ A → y ≺ᴸ a (suc n)
  go n (base q) b = ≼ᴸ-trans q (1≼Ω (toLv (x (suc n))))
  go n (plus {x = u₁} {y = u₂} σ c d) b =
    ΩPrin (suc n) σ (go n c (≼ᴸ-trans (s≼s (add-≽ˡ u₁ σ u₂)) b)) (go n d (≼ᴸ-trans (s≼s (add-≽ʳ u₁ σ u₂)) b))
  go n (cg e e′ c) b = ≼ᴸ-trans (s≼s e) (go n c (≼ᴸ-trans (s≼s e′) b))
  go n (col {u} {ξ = ξ} {x = w} cu cξ q r) b =
    let r′ : IsPsiᴸₐ u ξ (belowᴸ (a n) ξ q) w
        r′ = r
        fl = Ω-floorᴸ (belowᴸ (a n) ξ q) r′
        lt-u = ΩRefl u (≼ᴸ-trans (s≼s fl) b)
    in ≼ᴸ-trans (ltₐ (belowᴸ (a n) ξ q) r′) (ΩStep n u (Supᴸ.ub (H n) cu lt-u))

  open FixRow a A t H a≺a a≼A (λ n c q → go n c q) public

  ψ₀ΩΩ : IsPsiᴸ zero (Ω LΩ) (Tree.lim t)
  ψ₀ΩΩ = fix
```
