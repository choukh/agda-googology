# 一切深度 (五): 后继行, 对一切深度

> 接 [UniformNF3D3W](UniformNF3D3W.lagda.md). 结论先说:
>
> 1. **`Row.outR`: 帧在世界上好 (`rX`), 尾巴 $a$ 上的折叠对一切点好 (`ih`), 则 $a+1$ 上的折叠好.** 第 $m+1$ 份的头是帧副本 $P_m=F_a^{m+1}P$. $d$ 只是隐式参数, 证明不读它; $d=0$ 就是 `UniformNF3D2C.Row`.
> 2. **副本的世界 `w′`:** 点 $b_1$ 在 $w'$ 里, 当且仅当它压在一个 $X$ 的好点 $b^\dagger$ 之下, 且 $\forall O\in\mathcal P_1$, `fo1 O X (P,t) ∈ 𝓚` (`Bc`), 且 $P_0\,t\in\mathcal F_1$ (`Cc`).
> 3. **`RFm`: 副本在 $w'$ 上好, 用的吸收者只有 `clk`/`FlOver`.** D2U §4 怕的 "底抬高封闭性" 不需要: 副本只在头值压过 $F_a\,P\,s$ 的脊上被读 (`Rais` 的第二条), 而 $F_t\,P\,s'\sqsupseteq P\,s'\sqsupseteq$ 头值 $\sqsupseteq F_a\,P\,s$, 这正是 `FlOver a`.
> 4. D2C 的 `Cp` 没有了: `Bc` 同一个 $O$ 就够, 门槛由地板集 $\mathcal F_1$ 承担.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3R where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ)
open import OCF.Align.UniformNF3Eq using (_≅ˢ_)
open import OCF.Align.Uniform3Base using (Dem; Flr; _⊔_; Ev; InF; inl; inr; flo; cvFlo)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS)
open import OCF.Align.UniformNF3D3O using (Fr; Sp; sf; fold1; repU; rowU; Obs; fo1; run; _≈ᵒ_)
open import OCF.Align.UniformNF3D3G using (_⊑ᴱ_; Ctx; ctx-refl; FFl; FlU; FlU≈; SF; SF≈; fflF; flRep; leHd; F≅; B1₁ᴱ; ⊑ᴱ-trans; ≅→⊑ᴱ)
open import OCF.Align.UniformNF3D3N using (_⊑ᵒ_)
open import OCF.Align.UniformNF3D3C
open import OCF.Align.UniformNF3D3F using (FL; VF; ⊑ᴱ→ᵒ)
open import OCF.Align.UniformNF3D3S using (cxV; pT; mapV; putV; demUp; demFlo)
open import OCF.Align.UniformNF3D3W
```

## §0 `Rais` 的两个引理

```agda
raisAt : ∀ (d : ℕ) {φ fl} {X : Fr d φ} {P : Fr d fl} → FlU d P → ∀ {b s b′ s′} → Rais d X b s b′ s′ →
         (b′ ⊂ᵇ b) × (∀ {i ℓ} (e′ : Ev ℓ (sf (er s′) ⊔ fl)) (q : i <ᴵ ℓ) → (Σ (Ev ℓ (sf (er s) ⊔ φ)) λ e → X (er s) e q ⊑ᴱ P (er s′) e′ q) × 𝓕b b′ (P (er s′) e′ q))
raisAt zero hP ()
raisAt (suc d) {P = P} hP {b′ = b′} {s′ = s′@(fl′ , P′ , w′ , r′ , t′)} (sub , hb , hf) =
  sub , λ e′ q → (proj₁ (hb (proj₁ e′) q) , ⊑ᴱ-trans (proj₂ (hb (proj₁ e′) q)) (leHd {E = P} {Q = er s′} hP (sfW s′) e′ q)) ,
                 uF b′ (hf (proj₁ e′) q) (leHd {E = P} {Q = er s′} hP (sfW s′) e′ q)

raisM : ∀ (d : ℕ) {φ φ′} {X : Fr d φ} {X′ : Fr d φ′} {b b″ s b′ s′} → (b ⊂ᵇ b″) →
        (∀ {i ℓ} (e : Ev ℓ (sf (er s) ⊔ φ)) (q : i <ᴵ ℓ) → Σ (Ev ℓ (sf (er s) ⊔ φ′)) λ e″ → X′ (er s) e″ q ⊑ᴱ X (er s) e q) →
        Rais d X b s b′ s′ → Rais d X′ b″ s b′ s′
raisM zero i h ()
raisM (suc d) {b′ = b′} {s′ = s′@(fl′ , P′ , w′ , r′ , t′)} i h (sub , hb , hf) =
  (λ c → i (sub c)) , (λ e′ q → proj₁ (h (proj₁ (hb e′ q)) q) , ⊑ᴱ-trans (proj₂ (h (proj₁ (hb e′ q)) q)) (proj₂ (hb e′ q))) , hf
```

## §1 模块参数

`Qp t`: 脊 $(P,t)$. 下面的 $a$ 是尾巴, $b$ 留给点.

```agda
module Row {d flX} {X : Fr (suc d) flX} {wX : Wld (suc d)} (rX : RF (suc d) wX X)
           {k} (b₀ : Base) {fl} {P : Fr d fl} {w : Wld d} {rP : RF d w P} {s₀ : WSp d}
           (S₀ : SG b₀ (fl , P , w , rP , s₀)) (W₀ : wX b₀ (fl , P , w , rP , s₀))
           {i ℓ} {ev : Ev ℓ ((sf (er s₀) ⊔ fl) ⊔ (flX ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖′ : Cl i}
           (H₂ : ∀ {O} → 𝓖′ O → VF (𝓟b b₀) i O) (wt : Wit i 𝓖′) {a : Ordˢ k} (ea : a ≅ˢ a) (𝓚 : Cl k)
           (Kc : ∀ {O} → 𝓖′ O → 𝓚 (fo1 O X (fl , P , er s₀) ev p))
           (clk : ∀ {O C″} → 𝓚 O → FlOver a O C″ → 𝓚 C″)
           (cgk : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C)
           (ho : ∀ {C} → 𝓚 C → Hon k a C)
           (ih : ∀ b (s : WSp (suc d)) → SG b s → wX b s → ∀ {j ℓ₁} {ev₁ : Ev ℓ₁ (sf (er s) ⊔ (flX ⊔ flo k))} {p₁ : j <ᴵ ℓ₁} {𝓖₂ : Cl j} →
                 (∀ {O} → 𝓖₂ O → 𝓚 (fo1 O X (er s) ev₁ p₁)) → (∀ {O} → 𝓖₂ O → VF (𝓟b b) j O) → Wit j 𝓖₂ →
                 Good true 𝓖₂ (fold1 (flo k) (cvFlo k) X a (er s) ev₁ p₁)) where
  fF : FFl X
  fF = fX rX
  rE = FFl.rE fF
  ψf = flX ⊔ flo k
  Fb : Fr (suc d) ψf
  Fb = fold1 (flo k) (cvFlo k) X a
  fFb : FFl Fb
  fFb = fflF fF ea
  hP : FlU d P
  hP = fX rP
  Pm : ℕ → Fr d (fl ⊔ ψf)
  Pm m = repU P Fb (suc m)
  flP : ∀ m → FlU d (Pm m)
  flP m = flRep d hP fFb m

  Qp : WSp d → WSp (suc d)
  Qp t = fl , P , w , rP , t

  sfp : ∀ t → SF (er (Qp t))
  sfp t = hP , sfW t

  -- 环境的分量
  evX : ∀ {t : WSp d} {L} → Ev L (sf (er t) ⊔ (fl ⊔ ψf)) → Ev L (sf (er (Qp t)) ⊔ flX)
  evX e = (proj₁ e , proj₁ (proj₂ e)) , proj₁ (proj₂ (proj₂ e))

  evP : ∀ {t : WSp d} {L} → Ev L (sf (er t) ⊔ (fl ⊔ ψf)) → Ev L (sf (er t) ⊔ fl)
  evP e = proj₁ e , proj₁ (proj₂ e)

  evH : ∀ {t : WSp d} {L} → Ev L (sf (er t) ⊔ (fl ⊔ ψf)) → Ev L (sf (er (Qp t)) ⊔ ψf)
  evH e = (proj₁ e , proj₁ (proj₂ e)) , proj₂ (proj₂ e)
```

## §2 副本的序

```agda
  selfX : ∀ {Q : Sp (suc d)} → SF Q → ∀ {j L} (e : Ev L (sf Q ⊔ flX)) (q : j <ᴵ L) → X Q e q ≅ˢ X Q e q
  selfX sq e q = rE (SF≈ sq) e q e q (≅ᴵ-refl _)

  leX : ∀ (t : WSp d) {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → X (er (Qp t)) (evX {t} e) q ⊑ᴱ Pm 0 (er t) e q
  leX t e q = B1₁ᴱ {φ = flo k} {E = X} {Q = er (Qp t)} {cv = cvFlo k} {ev = evH {t} e} {p = q} (≅→⊑ᴱ (selfX (sfp t) (evX {t} e) q)) a ea

  leP : ∀ (t : WSp d) {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → P (er t) (evP {t} e) q ⊑ᴱ Pm 0 (er t) e q
  leP t e q = leHd {E = Fb} {Q = er (Qp t)} fFb (sfp t) (evH {t} e) q

  leS : ∀ m (t : WSp d) {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → Pm m (er t) e q ⊑ᴱ Pm (suc m) (er t) e q
  leS m t e q = leHd {E = Fb} {Q = _ , Pm m , er t} fFb (flP m , sfW t) (e , proj₂ (proj₂ e)) q

  leR : ∀ m (t : WSp d) {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → Pm 0 (er t) e q ⊑ᴱ Pm m (er t) e q
  leR zero    t e q = ≅→⊑ᴱ (FlU≈ d (flP 0) (SF≈ (sfW t)) e q e q (≅ᴵ-refl _))
  leR (suc m) t e q = ⊑ᴱ-trans (leR m t e q) (leS m t e q)
```

`kUp`: 吸收. 若 $P_0\,t\sqsubseteq X\,Q'$, 则 $Q'$ 为脊的上下文压在 $P_0\,t$ 之上, 所以在 `𝓚` 里. 这是 `clk` 对帧副本的唯一用法.

```agda
  kUp : ∀ (t : WSp d) {Q′ : Sp (suc d)} → SF Q′ → ∀ {j ℓ₃ ℓ₂} {e : Ev ℓ₃ (sf (er t) ⊔ (fl ⊔ ψf))} {q : j <ᴵ ℓ₃} {ev₂ : Ev ℓ₂ (sf Q′ ⊔ ψf)} {p₂ : j <ᴵ ℓ₂} {O : Obs j} → Ctx O →
        Pm 0 (er t) e q ⊑ᴱ X Q′ (proj₁ ev₂ , proj₁ (proj₂ ev₂)) p₂ →
        𝓚 (fo1 O X (er (Qp t)) (evH {t} e) q) → 𝓚 (fo1 O X Q′ ev₂ p₂)
  kUp t {Q′} sq {ev₂ = ev₂} {p₂ = p₂} {O = O} cO h K =
    clk K (flo-over (fF , sq , cO) (λ t′ et′ G → B1₁ᴱ {φ = flo k} {E = X} {Q = Q′} {cv = cvFlo k} {ev = ev₂} {p = p₂} h t′ et′ (ctx-refl O cO) G))
```

## §3 世界 `w′` 与 `RFm`

```agda
  Bc : Base → WSp d → Set
  Bc b₁ t = ∀ {j} {O : Obs j} → Ctx O → 𝓟b b₁ O → ∀ {ℓ₁} {ev₁ : Ev ℓ₁ (sf (er (Qp t)) ⊔ ψf)} {p₁ : j <ᴵ ℓ₁} → 𝓚 (fo1 O X (er (Qp t)) ev₁ p₁)

  Cc : Base → WSp d → Set
  Cc b₁ t = ∀ {j ℓ₁} (e : Ev ℓ₁ (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ ℓ₁) → 𝓕b b₁ (Pm 0 (er t) e q)

  w′ : Wld d
  w′ b₁ t = Σ Base λ b† → (b₁ ⊂ᵇ b†) × (SG b† (Qp t) × (wX b† (Qp t) × (Bc b₁ t × Cc b₁ t)))

  Cp : ∀ m → RF d w′ (Pm m) → WSp d → WSp (suc d)
  Cp m r t = (fl ⊔ ψf) , Pm m , w′ , r , t

  raiseK : ∀ m (r : RF d w′ (Pm m)) (t : WSp d) (b₁ : Base) → w′ b₁ t → SG b₁ t → (b‡ : Base) → b₁ ⊂ᵇ b‡ → SG b‡ (Qp t) → wX b‡ (Qp t) → wX b₁ (Cp m r t)
  raiseK m r t b₁ W₁ Sg b‡ sub SGt WXt =
    upX rX b‡ (Qp t) b₁ (Cp m r t) SGt WXt (b₁ , (λ c → c) , W₁ , Sg)
      (sub , (λ e q → evX {t} e , ⊑ᴱ-trans (leX t e q) (leR m t e q)) , (λ e q → uF b₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ W₁)))) e q) (leR m t e q)))

  RFm : ∀ m → RF d w′ (Pm m)
  vm : ∀ m b₁ (t : WSp d) → SG b₁ t → w′ b₁ t → ∀ {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → Wit j (VF (𝓟b b₁) j) → Good true (VF (𝓟b b₁) j) (Pm m (er t) e q)
  vm zero b₁ t Sg (b† , sub , SGt , WXt , Bk , Ck) {j} e q wv =
    ih b† (Qp t) SGt WXt {ev₁ = evH {t} e} {p₁ = q} {𝓖₂ = VF (𝓟b b₁) j} (λ c → Bk (cxV j c) (pT j c)) (λ c → mapV j sub c) wv
  vm (suc m) b₁ t Sg W₁@(b† , sub , SGt , WXt , Bk , Ck) {j} e q wv =
    ih b₁ (Cp m (RFm m) t) (b₁ , (λ c → c) , W₁ , Sg) (raiseK m (RFm m) t b₁ W₁ Sg b† sub SGt WXt)
       {ev₁ = e , proj₂ (proj₂ e)} {p₁ = q} {𝓖₂ = VF (𝓟b b₁) j}
       (λ c → kUp t {Q′ = _ , Pm m , er t} (flP m , sfW t) {e = e} {q = q} (cxV j c)
                (⊑ᴱ-trans (leR m t e q) (leHd {E = X} {Q = _ , Pm m , er t} fF (flP m , sfW t) (e , proj₁ (proj₂ (proj₂ e))) q))
                (Bk (cxV j c) (pT j c)))
       (λ c → c) wv

  dm : ∀ m b₁ (t : WSp d) → SG b₁ t → w′ b₁ t → ∀ {j L} {O : Obs j} → Ctx O → 𝓟b b₁ O → (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) (G : Goodᴺ (toZ (run O (Pm m (er t) e q)))) → ∀ {K} (r : InF K (sf (er t) ⊔ (fl ⊔ ψf))) → Dem (lvG G) r
  dm m b₁ t Sg (b† , sub , SGt , WXt , Bk , Ck) {O = O} cO π e q G r = dem′ r
    where
    L₀ = leR m t e q (ctx-refl O cO) G
    L₁ = leX t e q (ctx-refl O cO) (proj₁ L₀)
    up₀ : lvG (proj₁ L₀) ⊑ᴵ lvG G
    up₀ = toLevel-⊑ (forceᴺ-HS _ (proj₁ L₀)) (forceᴺ-HS _ G) (proj₂ L₀)
    up₁ : lvG (proj₁ L₁) ⊑ᴵ lvG G
    up₁ = ⊑ᴵ-trans (toLevel-⊑ (forceᴺ-HS _ (proj₁ L₁)) (forceᴺ-HS _ (proj₁ L₀)) (proj₂ L₁)) up₀
    dX′ : ∀ {K} (r′ : InF K ((sf (er t) ⊔ fl) ⊔ flX)) → Dem (lvG G) r′
    dX′ r′ = demUp r′ up₁ (dT rX b† (Qp t) SGt WXt cO (sub π) (evX {t} e) q (proj₁ L₁) r′)
    dem′ : ∀ {K} (r′ : InF K (sf (er t) ⊔ (fl ⊔ ψf))) → Dem (lvG G) r′
    dem′ (inl q₁) = dX′ (inl (inl q₁))
    dem′ (inr (inl q₂)) = dX′ (inl (inr q₂))
    dem′ (inr (inr (inl q₃))) = dX′ (inr q₃)
    dem′ (inr (inr (inr q₄))) = demFlo k q₄ (⊑ᴵ-trans (ho (Bk cO π {ev₁ = evH {t} e} {p₁ = q}) (proj₁ L₀)) up₀)

  flm : ∀ m b₁ (t : WSp d) → SG b₁ t → w′ b₁ t → ∀ {j L} (e : Ev L (sf (er t) ⊔ (fl ⊔ ψf))) (q : j <ᴵ L) → 𝓕b b₁ (Pm m (er t) e q)
  flm m b₁ t Sg (b† , sub , SGt , WXt , Bk , Ck) e q = uF b₁ (Ck e q) (leR m t e q)
```

`upm`: Kripke 单调. 新脊 $s_2$ 的头值压过 $P_m\,t$. `raisAt` 把 `Rais` 读成 "$P\,s_2$ 压过 $P_m\,t$ 且在新地板集里"; $d=0$ 的分支是空的, 全在那个引理里.

```agda
  upm : ∀ m b₁ (t : WSp d) b₂ (s₂ : WSp d) → SG b₁ t → w′ b₁ t → SG b₂ s₂ → Rais d (Pm m) b₁ t b₂ s₂ → w′ b₂ s₂
  upm m b₁ t b₂ s₂ Sg₁ (b† , sub , SGt@(b‡ , sub‡ , W‡ , Sg‡) , WXt , Bk , Ck) Sg₂ R = b₂ , (λ c → c) , (b₂ , (λ c → c) , WP , Sg₂) , WX₂ , Bk₂ , Ck₂
    where
    A = raisAt d {X = Pm m} {P = P} hP {b = b₁} {s = t} {b′ = b₂} {s′ = s₂} R
    sub₂ = proj₁ A
    f = proj₂ A
    WP : w b₂ s₂
    WP = upX rP b‡ t b₂ s₂ Sg‡ W‡ Sg₂ (raisM d {X = Pm m} {X′ = P} {b = b₁} {b″ = b‡} {s = t} {b′ = b₂} {s′ = s₂} (λ c → sub‡ (sub c)) (λ e q → evP {t} e , ⊑ᴱ-trans (leP t e q) (leR m t e q)) R)
    WX₂ : wX b₂ (Qp s₂)
    WX₂ = upX rX b† (Qp t) b₂ (Qp s₂) SGt WXt (b₂ , (λ c → c) , WP , Sg₂)
      ((λ c → sub (sub₂ c)) ,
       (λ e′ q → evX {t} (proj₁ (proj₁ (f e′ q))) , ⊑ᴱ-trans (leX t _ q) (⊑ᴱ-trans (leR m t _ q) (proj₂ (proj₁ (f e′ q))))) ,
       (λ e′ q → proj₂ (f e′ q)))
    Bk₂ : Bc b₂ s₂
    Bk₂ cO π {ev₁ = ev₁} {p₁ = p₁} =
      kUp t {Q′ = er (Qp s₂)} (sfp s₂) {e = proj₁ (proj₁ (f (proj₁ ev₁) p₁))} {q = p₁} {ev₂ = ev₁} {p₂ = p₁} cO
        (⊑ᴱ-trans (leR m t _ p₁) (⊑ᴱ-trans (proj₂ (proj₁ (f (proj₁ ev₁) p₁))) (leHd {E = X} {Q = er (Qp s₂)} fF (sfp s₂) (proj₁ ev₁ , proj₁ (proj₂ ev₁)) p₁)))
        (Bk cO (sub₂ π))
    Ck₂ : Cc b₂ s₂
    Ck₂ e q = uF b₂ (proj₂ (f (evP {s₂} e) q)) (leP s₂ e q)

  RFm m = rfp (flP m) (vm m) (dm m) (flm m) (upm m)
```

## §4 基点与输出

`b₁`: $\mathcal P_1=\mathcal P_0\wedge$ `Kp`, $\mathcal F_1=$ "压在 $P_0\,s_0$ 之上". 封闭性的两半: $\mathcal P_0$ 部分用 $X$ 在 $b_0$ 的地板集 (`flX`), `Kp` 部分用 `clk`.

```agda
  rQ₀ = SF≈ (sfp s₀)
  Q₀ = er (Qp s₀)

  Kp : ∀ {j} → Obs j → Set
  Kp {j} O = ∀ {ℓ₁} {ev₁ : Ev ℓ₁ (sf Q₀ ⊔ ψf)} {p₁ : j <ᴵ ℓ₁} → 𝓚 (fo1 O X Q₀ ev₁ p₁)

  𝓟₁ : ∀ {j} → Obs j → Set
  𝓟₁ O = 𝓟b b₀ O × Kp O

  𝓕₁ : ∀ {j} → Ordˢ j → Set
  𝓕₁ {j} x = Σ Ordᴵ λ L → Σ (Ev L (sf (er s₀) ⊔ (fl ⊔ ψf))) λ e → Σ (j <ᴵ L) λ q → Pm 0 (er s₀) e q ⊑ᴱ x

  b₁ : Base
  b₁ = base 𝓟₁
    (λ c₀ o (π , κ) → pCb b₀ c₀ o π , (λ {ℓ₁} {ev₁} {p₁} → cgk (fF , sfp s₀ , c₀) (fo1 {ev = ev₁} {ev′ = ev₁} {p = p₁} {p′ = p₁} o rE rQ₀) (κ {ev₁ = ev₁} {p₁ = p₁})))
    𝓕₁
    (λ (L , e , q , h) h′ → L , e , q , ⊑ᴱ-trans h h′)
    (λ {x₁} {x₂} {x₃} {O} {C″} (L , e , q , h) cO (π , κ) cC fl′ →
       cl b₀ (uF b₀ (RFP.flX rX b₀ (Qp s₀) S₀ W₀ (evX {s₀} e) q) (⊑ᴱ-trans (leX s₀ e q) h)) cO π cC fl′ ,
       (λ {ℓ₁} {ev₁} {p₁} → clk (κ {ev₁ = evH {s₀} e} {p₁ = q}) (flo-over (fF , sfp s₀ , cC) (λ t′ et′ G →
          let R₁ = fl′ _ (F≅ {ev = ev₁} {ev′ = ev₁} rE rQ₀ et′ p₁ p₁ (≅ᴵ-refl _)) G
              R₂ = h (ctx-refl O cO) (proj₁ R₁)
          in proj₁ R₂ , ⊑-trans (proj₂ R₂) (proj₂ R₁)))))

  S₁ : SG b₁ s₀
  S₁ = SG-anti s₀ (λ c → proj₁ (proj₂ S₀) (proj₁ c)) (proj₂ (proj₂ (proj₂ S₀)))

  W₁ : w′ b₁ s₀
  W₁ = b₀ , proj₁ , S₀ , W₀ , (λ cO π → proj₂ π) , (λ e q → _ , e , q , ≅→⊑ᴱ (FlU≈ d (flP 0) (SF≈ (sfW s₀)) e q e q (≅ᴵ-refl _)))

  inj : ∀ {O} → 𝓖′ O → VF 𝓟₁ i O
  inj {O} c = putV {𝓟 = 𝓟b b₀} {𝓠 = 𝓟₁} i (pT i (H₂ c) , (λ {ℓ₁} {ev₁} {p₁} → cgk (fF , sfp s₀ , cO) (fo1 {ev = ev₁} {ev′ = ev} {p = p₁} {p′ = p} (ctx-refl O cO) rE rQ₀) (Kc c))) (H₂ c)
    where cO = cxV i (H₂ c)

  wit-map′ : Wit i 𝓖′ → Wit i (λ O → 𝓖′ O)
  wit-map′ w₀ = w₀

  evA : Ev ℓ (sf (er s₀) ⊔ (fl ⊔ ψf))
  evA = proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)

  outR : Good true 𝓖′ (fold1 (flo k) (cvFlo k) X (Ord₊ˢ.suc a) Q₀ ev p)
  outR = bl hh mo
    where
    hh : ∀ m → Good true 𝓖′ (rowU Q₀ Fb m ev p)
    hh zero = Good-mono (λ c → mapV i (proj₁ (proj₂ S₀)) (H₂ c))
      (vX rP (proj₁ S₀) s₀ (proj₂ (proj₂ (proj₂ S₀))) (proj₁ (proj₂ (proj₂ S₀))) (evP {s₀} evA) p (wit-map i (λ c → mapV i (proj₁ (proj₂ S₀)) (H₂ c)) wt))
    hh (suc zero) = ih b₀ (Qp s₀) S₀ W₀ {ev₁ = ev} {p₁ = p} {𝓖₂ = 𝓖′} Kc H₂ wt
    hh (suc (suc m)) = ih b₁ (Cp m (RFm m) s₀) (b₁ , (λ c → c) , W₁ , S₁) (raiseK m (RFm m) s₀ b₁ W₁ S₁ b₀ proj₁ S₀ W₀)
       {ev₁ = evA , proj₂ ev} {p₁ = p} {𝓖₂ = 𝓖′}
       (λ c → kUp s₀ {Q′ = _ , Pm m , er s₀} (flP m , sfW s₀) {e = evA} {q = p} (cxV i (H₂ c))
                (⊑ᴱ-trans (leR m s₀ evA p) (leHd {E = X} {Q = _ , Pm m , er s₀} fF (flP m , sfW s₀) (evA , proj₁ (proj₂ (proj₂ evA))) p))
                (proj₂ (pT i (inj c))))
       inj (wit-map′ wt)
    mo : ∀ m → rowU Q₀ Fb m ev p ⊑ᵒ rowU Q₀ Fb (suc m) ev p
    mo zero = ⊑ᴱ→ᵒ (FlU≈ d hP (SF≈ (sfW s₀)) _ p _ p (≅ᴵ-refl _)) (leP s₀ evA p)
    mo (suc m) = ⊑ᴱ→ᵒ (FlU≈ d (flP m) (SF≈ (sfW s₀)) evA p evA p (≅ᴵ-refl _)) (leS m s₀ evA p)
```
