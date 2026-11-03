# 判决的规格: 证据给出判决 (底座)

> 底座, 不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md).
>
> - 字面的 `CV` 太窄: 有的层号对上**没有**任何判决 `CV` 正确 (`no-cv`); 要它处处有解就推出函数外延性的一个实例 (`cv-total→ext`). 所以要放宽到 `CVx`.
> - 证据 $(c,\ \mathtt{WF}^\mathsf{A}\,c,\ p,\ q,\ \text{可容许})$ **计算**判决 (`decide`). 上升的正确性不要 `WF`, 只要良基 (`all-ac`).
> - `CVx` 比的是写法, 不是序数值: $\omega$ 与 $\omega'=[1,2,\dots]$ 互相 $\sqsubseteq$, 但 `CVx` 对 $(\omega,\omega'+1)$ 强制 `rise`, 对 $(\omega',\omega'+1)$ 强制穿透 (`trap`). **这个层号对上判决正确但树与值不一致** (`trap-tree₁`, `trap-tree₂`); 它们没有公共的好上界 (`no-bound`), 所以证据把这种对排除在外.
> - 放宽之后一个原始的 `S` 对一切 `Ordᴵ` 层号仍不能正确 (`no-uniformˣ`, WLPO).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecEvid where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Verdict; pen; rise; toLv; _+_; Ω)
open import OCF.Align.InaccFloorTree using (Sib; natL; sib; module PF)
open import OCF.Align.InaccThetaRel using (module Leaf)
open import OCF.Align.InaccThetaEq using (module Eqv)
open import Data.Bool using (Bool; true; false)
open import OCF.Align.VerdictSpecBase using (module Eqx; coe⁺)
open import OCF.Align.InaccSingularBase using (WLPO)
open import OCF.Align.InaccThetaNeg using (E; κ; G; i; flag; flag-false; flag-true; sel; at-natE; tF; tT)
open import OCF.Align.Level using (ωᴵ)
import OCF.Align.Level as Lvl
open import OCF.Align.VerdictSpecUniq using (Kd; kp; kr; kd; at-n)
open import OCF.Align.VerdictSpecReject using (Ω₁; LΩ; A₂; q₂; S₁)
```

## §1 字面的 `CV` 太窄

**`no-cv`.** $B_0$ 只含 0. 两个 `limᴼ 0` 在 $B_0$ 上相同, 在 $B_0$ 外不同, 所以 $\approx^\mathsf{B}$ 但不字面相等. 上升错 (目标里有 $\approx$ 的路径), 穿透也错 (没有字面的路径).

```agda
private
  𝟎 : Ordᴸ zero
  𝟎 = Tree.zero
  𝟏₀ : Ordᴸ zero
  𝟏₀ = Tree.suc Tree.zero

  g₀ g₁ : Ordᴸ zero → Lv
  g₀ _ = zero
  g₁ Tree.zero = zero
  g₁ (Tree.suc _) = suc zero
  g₁ (Tree.lim _) = suc zero

module NoCV (S : Sib) where
  B₌ : Ordᴸ zero → Set
  B₌ x = x ≡ Tree.zero
  open Eqv S B₌

  j₀ i₀ : Lv
  j₀ = limᴼ zero g₀
  i₀ = suc (limᴼ zero g₁)

  j≈ : j₀ ≈ᴮ limᴼ zero g₁
  j≈ = o≈ (λ { _ refl → z≈ })

  ev₁ : Lv → Lv
  ev₁ (limᴼ zero g) = g 𝟏₀
  ev₁ _ = zero

  z≢ : _≡_ {A = Lv} (suc zero) zero → ⊥
  z≢ ()

  no-cv : (v : Verdict j₀ i₀) → CV v → ⊥
  no-cv _ (cvp (inj₁ _) e _) = z≢ (cong ev₁ e)
  no-cv _ (cvp (inj₂ (inj₁ (inj₁ _))) () _)
  no-cv _ (cvp (inj₂ (inj₂ (Tree.suc _ , inj₁ _))) () _)
  no-cv _ (cvp (inj₂ (inj₂ (Tree.lim _ , inj₁ _))) () _)
  no-cv _ (cvr k) = k (inj₁ tt) tt (≈ᴮ-sym j≈)
```

**`cv-total→ext`.** 要 `CV` 在 $\lim(\mathtt{natL}\circ h)$ 与 $\lim(\mathtt{natL}\circ h')+1$ 上有解, 就要 $\mathtt{natL}\circ h\equiv\mathtt{natL}\circ h'$, 哪怕 $h,h'$ 只是逐点相等. 这是函数外延性, `--without-K` 下不可证.

```agda
module LitExt (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqv S B₀

  nl : ∀ m {f : ℕ → Lv} → natL m ≡ lim f → ⊥
  nl zero ()
  nl (suc m) ()

  unl : Lv → ℕ → Lv
  unl (lim f) = f
  unl _       = λ _ → zero

  cv-total→ext : (∀ j i → Σ (Verdict j i) CV) → (h h′ : ℕ → ℕ) → (∀ n → h n ≡ h′ n) →
                 (λ n → natL (h′ n)) ≡ (λ n → natL (h n))
  cv-total→ext tot h h′ eq with tot (lim (λ n → natL (h n))) (suc (lim (λ n → natL (h′ n))))
  ... | _ , cvr k = ⊥-elim (k (inj₁ tt) tt (l≈ (λ n → subst (λ u → natL (h′ n) ≈ᴮ natL u) (sym (eq n)) (≈ᴮ-refl _))))
  ... | _ , cvp (inj₁ _) e _ = cong unl e
  ... | _ , cvp (inj₂ (n , r)) e _ with at-n (h′ n) r
  ...   | m , e′ = ⊥-elim (nl m (trans (sym e′) e))
```

## §2 上升的正确性只要良基

`Ac`: 良基性对层号结构递归, 对一切层号成立, 不要 `WF`. 这里取 `A = Bs`, 所以可容许就是 `AdmB`. (`A` 比 `Bs` 窄时, `WF` 的三歧给不出 `cvr`, 因为 `cvr` 要否定全部 `AdmB` 路径.)

```agda
module Ev (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqx S B₀
  open RelB Bs (λ _ _ a → a)

  data Ac (a : Lv) : Set where
    ac : (∀ b → b ≺ᴬ a → Ac b) → Ac a

  below : ∀ a b → b ≺ᴬ a → Ac b
  below (suc k) b (viaᴬ (inj₁ _) _ e) = ac λ c c≺b → below k c (≺ᴬ-respʳ c≺b e)
  below (suc k) b (viaᴬ (inj₂ r) d e) = below k b (viaᴬ r d e)
  below (lim f) b (viaᴬ (n , r) d e) = below (f n) b (viaᴬ r d e)
  below (limᴼ k g) b (viaᴬ (inj₁ (inj₁ _)) _ e) = ac λ c c≺b → below k c (≺ᴬ-respʳ c≺b e)
  below (limᴼ k g) b (viaᴬ (inj₁ (inj₂ r)) d e) = below k b (viaᴬ r d e)
  below (limᴼ k g) b (viaᴬ (inj₂ (x , r)) (a , d) e) = below (g x) b (viaᴬ r d e)

  all-ac : ∀ a → Ac a
  all-ac a = ac (below a)

  irr : ∀ {a} → Ac a → a ≺ᴬ a → ⊥
  irr (ac h) p = irr (h _ p) p

  noCyc : ∀ {a b} → Ac a → a ≺ᴬ b → b ≺ᴬ a → ⊥
  noCyc (ac h) p q = noCyc (h _ q) q p

  P0-at : ∀ c → P0 c → ∀ r → AdmB c r → P0 (at c r)
  P0-at (suc k) w (inj₁ _) _ = w
  P0-at (suc k) w (inj₂ r) d = P0-at k w r d
  P0-at (lim f) w (n , r) d = P0-at (f n) (w n) r d
  P0-at (limᴼ zero g) w (inj₁ (inj₁ _)) _ = tt
  P0-at (limᴼ zero g) w (inj₂ (x , r)) (a , d) = P0-at (g x) (w x a) r d
```

## §3 证据给出判决

`decide` 是本文的主结论: 输入是证书式的 (公共上界的 `WF`, 两条可容许路径), 输出是判决与它的正确性. 它不测试任何东西, 只是 `<-decᴬ`. 穿透时路径是三歧给的, 搬运是 `coe⁺`. `decide-kind`: 任何正确的判决都与它同种类.

```agda
  rise-of-≺ : ∀ {j i} → i ≺ᴬ j → ∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥
  rise-of-≺ {j} {i} h r d e = noCyc (all-ac i) (≺ᴬ-respʳ h (≈ᴮ-sym e)) (viaᴬ r d (≈ᴮ-refl _))

  rise-of-≈ : ∀ {j i} → j ≈ᴮ i → ∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥
  rise-of-≈ {j} {i} q r d e = irr (all-ac i) (viaᴬ r d (≈ᴮ-sym (≈ᴮ-trans e q)))

  decide : ∀ c → WFᴬ c → P0 c → (p q : Pre c) → AdmB c p → AdmB c q → Σ (Verdict (at c p) (at c q)) CVx
  decide c w z p q dp dq with <-decᴬ c w p q dp dq
  ... | injᵃ (viaᴬ r d e) = pen r (coe⁺ (at (at c q) r) (at c p)) ,
        cvp r _ d e (bc (P0-at (at c q) (P0-at c z q dq) r d) (P0-at c z p dp))
  ... | injᵇ h = rise , cvr (rise-of-≺ h)
  ... | injᶜ q′ = rise , cvr (rise-of-≈ q′)

  -- 没有路径就是上升, 不要上界
  rise≠path : ∀ {j i} {v : Verdict j i} → (∀ (r : Pre i) → AdmB i r → j ≈ᴮ at i r → ⊥) → CVx v → kd v ≡ kr
  rise≠path n (cvp r _ a e _) = ⊥-elim (n r a e)
  rise≠path n (cvr _) = refl
```

## §4 `CVx` 比的是写法

$\omega$ 与 $\omega'=[1,2,3,\dots]$ 互相 $\sqsubseteq^\mathsf{A}$ (`ω⊑ω′`, `ω′⊑ω`): 按观测它们是同一个序数. 但 $\omega$ 不 $\approx$ 目标 $\omega'+1$ 的任何前驱, 所以判决被迫上升 (`trap₁`), 而 $\omega'$ 被迫穿透 (`trap₂`). 这两个输入给的 $\psi$ 的种类不同: 一个是 `limᵢ`, 一个是 $\omega$-极限. 这是一棵 **判决全部正确、但在 $\sqsubseteq$-等价的输入上不一致** 的树. 解救在 `no-bound`: $\omega$ 与 $\omega'$ 不能同时是一个好上界的可容许前驱. 所以规格的定义域是有好上界的层号对, 不是全部原始对.

```agda
ω₀ ω₁ : Lv
ω₀ = lim natL
ω₁ = lim (λ n → natL (suc n))

module Trap (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Ev S B₀
  open Eqx S B₀
  open RelB Bs (λ _ _ a → a)

  nat≉ : ∀ m {f} → natL m ≈ᴮ lim f → ⊥
  nat≉ zero ()
  nat≉ (suc m) ()

  ≉nat : ∀ m {f} → lim f ≈ᴮ natL m → ⊥
  ≉nat zero ()
  ≉nat (suc m) ()

  at≈ : ∀ m {f} (r : Pre (natL m)) → lim f ≈ᴮ at (natL m) r → ⊥
  at≈ m r e with at-n m r
  ... | m′ , e′ = ≉nat m′ (subst (_ ≈ᴮ_) e′ e)

  self : ∀ n → natL n ⊑ᴬ natL (suc n)
  self n r d = viaᴬ (inj₂ r) d (≈ᴮ-refl _)

  ω⊑ω′ : ω₀ ⊑ᴬ ω₁
  ω⊑ω′ (n , r) d = viaᴬ (n , inj₂ r) d (≈ᴮ-refl _)

  ≺-at : ∀ m (r : Pre (natL (suc m))) → (Σ (Pre (natL m)) λ r′ → at (natL m) r′ ≡ at (natL (suc m)) r) ⊎ (at (natL (suc m)) r ≡ natL m)
  ≺-at m (inj₁ _) = inj₂ refl
  ≺-at m (inj₂ r) = inj₁ (r , refl)

  ω′⊑ω : ω₁ ⊑ᴬ ω₀
  ω′⊑ω (n , r) d = viaᴬ (suc n , r) d (≈ᴮ-refl _)

  z≉1 : zero ≈ᴮ suc zero → ⊥
  z≉1 ()

  1≉z : suc zero ≈ᴮ zero → ⊥
  1≉z ()

  trap₁ : ∀ (v : Verdict ω₀ (suc ω₁)) → CVx v → kd v ≡ kr
  trap₁ v = rise≠path λ where
    (inj₁ _) d (l≈ h) → z≉1 (h 0)
    (inj₂ (n , r)) d e → at≈ (suc n) r e

  trap₁-ok : CVx {ω₀} {suc ω₁} rise
  trap₁-ok = cvr λ where
    (inj₁ _) d (l≈ h) → 1≉z (h 0)
    (inj₂ (n , r)) d e → at≈ (suc n) r (≈ᴮ-sym e)

  trap₂ : ∀ (v : Verdict ω₁ (suc ω₁)) → CVx v → kd v ≡ kp
  trap₂ _ (cvp _ _ _ _ _) = refl
  trap₂ _ (cvr k) = ⊥-elim (k (inj₁ tt) tt (≈ᴮ-refl _))

  -- 没有公共的好上界
  ¬tri : Tri ω₀ ω₁ → ⊥
  ¬tri (injᵃ (viaᴬ (n , r) _ e)) = at≈ (suc n) r e
  ¬tri (injᵇ (viaᴬ (n , r) _ e)) = at≈ n r e
  ¬tri (injᶜ (l≈ h)) with h 0
  ... | ()

  no-bound : ∀ c → WFᴬ c → (p q : Pre c) → AdmB c p → AdmB c q → at c p ≈ᴮ ω₀ → at c q ≈ᴮ ω₁ → ⊥
  no-bound c w p q dp dq e e′ = ¬tri (shL (≈ᴮ-sym e) (shR (≈ᴮ-sym e′) (<-decᴬ c w p q dp dq)))
```

**树也不一致.** `ψ` 的目标取 $\omega'+1$, 模式 `sib`, 输入 $\Omega_{\omega+1}$ 与 $\Omega_{\omega'+1}$. 判决都正确时, 前者是 $\omega$-极限 (`trap-tree₁`), 后者是 `limᵢ` (`trap-tree₂`). 这就是判据**拒绝不了**的不一致, 只有 `no-bound` 能把它排除.

```agda
data HL : Set where
  hl0 hl1 hll hli hlu : HL

hL : ∀ {i} → Ordᴸ i → HL
hL Tree.zero    = hl0
hL (Tree.suc _) = hl1
hL (Tree.lim _) = hll
hL (limᵢ _ _)   = hli
hL (up _ _)     = hlu

module TrapTree (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Trap S B₀
  open Eqx S B₀

  kp≠kr : kp ≡ kr → ⊥
  kp≠kr ()

  trap-tree₁ : CVx (S ω₀ (suc ω₁)) → hL (ψᵖ {suc ω₀} {suc ω₁} sib (Ω (suc ω₀))) ≡ hll
  trap-tree₁ cv with S ω₀ (suc ω₁) | cv
  ... | rise | _ = refl
  ... | pen r b | c = ⊥-elim (kp≠kr (trap₁ _ c))

  trap-tree₂ : CVx (S ω₁ (suc ω₁)) → hL (ψᵖ {suc ω₁} {suc ω₁} sib (Ω (suc ω₁))) ≡ hli
  trap-tree₂ cv with S ω₁ (suc ω₁) | cv
  ... | pen r b | _ = refl
  ... | rise | c = ⊥-elim (kp≠kr (sym (trap₂ _ c)))
```

## §5 真实的第一对: 证据算出手给的判决

`S` 第一次被问到的是 $(\Omega,\Omega+1)$ ([VerdictSpecReject](VerdictSpecReject.lagda.md) §1). 这里给 $\Omega\cdot2$ 的层号一个证书, 世界 `B₂` 只含 1, 2. `first-is-S₁`: `decide` 在这一对上**算出来的就是** `S₁` 的答案, `refl`. 所以手给的判决不是手给的: 它是证书的函数. 世界是有限的, 只说明机制; 更大的世界要更大的证书.

```agda
private
  𝟐 : Ordᴸ zero
  𝟐 = Tree.suc 𝟏₀

module Real (S : Sib) where
  B₂ : Ordᴸ zero → Set
  B₂ x = (x ≡ 𝟏₀) ⊎ (x ≡ 𝟐)

  open Ev S B₂
  open Eqx S B₂
  open RelB Bs (λ _ _ a → a)

  tl⊑ : ∀ x → B₂ x → toLv x ⊑ᴬ toLv 𝟐
  tl⊑ _ (inj₁ refl) (inj₁ _) _ = viaᴬ (inj₂ (inj₁ tt)) tt z≈
  tl⊑ _ (inj₂ refl) r d = viaᴬ r d (≈ᴮ-refl _)

  wf-tl : ∀ x → B₂ x → WFᴬ (toLv x)
  wf-tl _ (inj₁ refl) = tt
  wf-tl _ (inj₂ refl) = tt

  wf-LΩ : WFᴬ LΩ
  wf-LΩ = (λ x y ax ay → 𝟐 , inj₂ refl , tl⊑ x ax , tl⊑ y ay) ,
          (𝟏₀ , inj₁ refl , viaᴬ (inj₁ tt) tt z≈ , (λ ())) ,
          wf-tl

  g⊑ : ∀ x → B₂ x → toLv (Ω₁ + up tt x) ⊑ᴬ toLv (Ω₁ + up tt 𝟐)
  g⊑ _ (inj₁ refl) r d = viaᴬ (inj₂ r) d (≈ᴮ-refl _)
  g⊑ _ (inj₂ refl) r d = viaᴬ r d (≈ᴮ-refl _)

  wf-g : ∀ x → B₂ x → WFᴬ (toLv (Ω₁ + up tt x))
  wf-g _ (inj₁ refl) = wf-LΩ
  wf-g _ (inj₂ refl) = wf-LΩ

  wf-A₂ : WFᴬ A₂
  wf-A₂ = (λ x y ax ay → 𝟐 , inj₂ refl , g⊑ x ax , g⊑ y ay) ,
          (𝟏₀ , inj₁ refl , viaᴬ (inj₂ (inj₁ (inj₁ tt))) tt z≈ , (λ ())) ,
          wf-g

  p0-LΩ : P0 LΩ
  p0-LΩ _ (inj₁ refl) = tt
  p0-LΩ _ (inj₂ refl) = tt

  p0-A₂ : P0 A₂
  p0-A₂ _ (inj₁ refl) = p0-LΩ
  p0-A₂ _ (inj₂ refl) = p0-LΩ

  p₁ : Pre A₂
  p₁ = inj₂ (𝟏₀ , inj₁ tt)

  d₁ : AdmB A₂ p₁
  d₁ = inj₁ refl , tt

  d₂ : AdmB A₂ q₂
  d₂ = inj₂ refl , tt

  first-pair : Σ (Verdict LΩ (suc LΩ)) CVx
  first-pair = decide A₂ wf-A₂ p0-A₂ p₁ q₂ d₁ d₂

  first-is-S₁ : proj₁ first-pair ≡ S₁ LΩ (suc LΩ)
  first-is-S₁ = refl

  second-pair : Σ (Verdict LΩ LΩ) CVx
  second-pair = decide A₂ wf-A₂ p0-A₂ p₁ p₁ d₁ d₁

  second-is-S₁ : proj₁ second-pair ≡ S₁ LΩ LΩ
  second-is-S₁ = refl
```

## §6 放宽不绕过 `no-uniform`

[InaccThetaNeg](InaccThetaNeg.lagda.md) 的 `no-uniform` 是对字面的 `CV` 证的. `CVx` 更宽, 要重新问一遍: 一个拿原始层号对的 `S` 能不能对一切 `Ordᴵ` 层号 `CVx` 正确? 不能, 还是 WLPO (`no-uniformˣ`), 证明同形. 所以要证据不是字面性的产物.

```agda
module NegX (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Eqx S B₀

  J : Lv
  J = E (Lvl.suc ωᴵ)

  I : (ℕ → Bool) → Lv
  I s = E (Lvl.suc (i s))

  read : ∀ s → LvT (κ s) → CVx (S J (I s))
  read s w with proj₁ w (1 , inj₁ tt) tt
  ... | inj₂ (ok , _) = proj₁ ok (0 , inj₁ tt) tt

  J≉nat : ∀ m → J ≈ᴮ natL m → ⊥
  J≉nat (suc m) (s≈ e) = lim≉ m e where
    lim≉ : ∀ m {f : ℕ → Lv} → lim f ≈ᴮ natL m → ⊥
    lim≉ zero ()
    lim≉ (suc m) ()

  no-pen : ∀ s → (∀ n → s n ≡ false) → ∀ (r : Pre (I s)) → J ≈ᴮ at (I s) r → ⊥
  no-pen s h (inj₁ _) ()
  no-pen s h (inj₂ (n , r)) e = go (flag s n) (flag-false s h n) r e where
    go : ∀ b → b ≡ false → (r : Pre (E (sel b n))) → J ≈ᴮ at (E (sel b n)) r → ⊥
    go _ refl r e with at-natE n r
    ... | m , e′ = J≉nat m (subst (J ≈ᴮ_) e′ e)

  yes-path : ∀ b n → b ≡ true → Σ (Pre (E (sel b n))) λ r → AdmB (E (sel b n)) r × at (E (sel b n)) r ≈ᴮ J
  yes-path _ n refl = inj₁ tt , tt , ≈ᴮ-refl J

  dec : ∀ s (v : Verdict J (I s)) → ((∀ n → s n ≡ false) → CVx v) → (∀ n → s n ≡ true → CVx v) →
        (∀ n → s n ≡ false) ⊎ ((∀ n → s n ≡ false) → ⊥)
  dec s (pen r b) c₁ c₂ = inj₂ λ h → absurd h (c₁ h) where
    absurd : (∀ n → s n ≡ false) → CVx (pen r b) → ⊥
    absurd h (cvp _ _ _ e _) = no-pen s h r e
  dec s rise c₁ c₂ = inj₁ λ n → go n (s n) refl where
    go : ∀ n b → s n ≡ b → s n ≡ false
    go n false p = p
    go n true  p with c₂ n p
    ... | cvr k with yes-path (flag s n) n (flag-true s n p)
    ...   | r , d , e = ⊥-elim (k (inj₂ (n , r)) d e)

  no-uniformˣ : (∀ a → LvT (E a)) → WLPO
  no-uniformˣ H s = dec s (S J (I s))
    (λ h → read s (H (Lvl.lim (G s) (tF s h))))
    (λ n p → read s (H (Lvl.lim (G s) (tT s n p))))
```
