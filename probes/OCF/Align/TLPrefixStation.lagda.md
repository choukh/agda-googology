# 前缀 (二): 世界前缀在 $\psi_0(\Omega_\Omega)$ 不改序数值

> 入口 [TLPrefix](TLPrefix.lagda.md). **验收文件, 读 `NoCumsum`, `BTBOFull`. 判决: HOLDS (序数值验收, 主档).** `TᵖΩ := Tᵖ 1 0 one`: [NoCumPre](NoCumPre.lagda.md) 那棵带世界前缀 $u+\mathrm{rd}\,y$ 的树, $u=1$. 主定理 `TᵖΩ≈ : fr TᵖΩ ≈ᵛ BTBOᴵ`, `TᵖΩ≈T⁰`.
>
> 不用累加的机器 (`cumsum`, `Eb-plus`). 只有一条通用的 `Cross`: 两个严格的层号 $a\preccurlyeq b$ 就有 $\psi^0(\Omega_a)\preccurlyeq\psi^0(\Omega_{\mathrm{lv}\,\psi^0(\Omega_b)})$. 代价是跳一格, 所以比较是交错的 (`upp`: $z_k\preccurlyeq\gamma_{3k+1}$, `lw`: $\gamma_{k+1}\preccurlyeq z_{2k}$), 不是逐项的. 前缀只提供三件事: 严格性 (`SV-1⊕`), $a\preccurlyeq 1+a$ (`f≼`), $1+a\preccurlyeq a+1$ (`f⊕≼`). **$1+a\preccurlyeq a+1$ 对一切 $a$ 成立**, 这是 $u=1$ 这一站专有的; $u$ 大时没有对应的界 (`no-⊕≼`, [TLPrefixVal](TLPrefixVal.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixStation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼; ≺→s≼)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValNeg using (HS-≅)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-L; St-≅; St-F; SV-toLevel; Pos; ps; pl; pos-L; z<SV)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.BTBOFullEb using (V2)
open import OCF.Align.BTBOFullV3 using (V3; bkᴵ; Fʸ; Fstep)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFull using (tr₀-bk; St-bk; γ-step)
open import OCF.Align.BTBOValAbsorb using (St)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; Ix-r; fr; Y-sim)
open import OCF.Align.NoCumLit using (Ord₀; rd; _≈ᴬ_; _⊴₀_; r0; s0; l0; Lit₀)
open import OCF.Align.NoCumW using (one; g₀; lgw; Tᴰ; Ω̇)
open import OCF.Align.NoCumPre using (G; gw; gc; force; outs; Tᵖ; G-Tᵖ; _⊞_; Lit-force)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.NoCumAcceptOmega using (Ix-rd; Ix-≈; T⁰≅; term)
open import OCF.Align.TLPrefixBridge using (force-Y; Q-Ω; qw)
```

## §1 $\psi^0\Omega$ 对值单调, 跳一格

```agda
Cross : ∀ {a b} → SV a → SV b → forget a ≼ forget b → (h : HS (Fʸ b)) → Fʸ a ≼ Fʸ (toLevel (Fʸ b) h)
Cross {a} {b} sa sb w h =
  ≼-trans (Ψ-emb (PW₃ (V1 sa)))
  (≼-trans (Ψ-emb (PW₁ (V2 (bkᴵ a) (bkᴵ b) (St-bk sa) (St-bk sb)
                        (≼-trans (≅→≼ (tr₀-bk a)) (≼-trans w (≅→≼ (≅-sym (tr₀-bk b))))))))
           (Ψ-emb (PW₂ h (V3 sb))))
```

## §2 层号上的 $1+$

```agda
_⊕_ : Ordᴵ → Ordᴵ → Ordᴵ
⊕-mono : ∀ a {x y} → x ⊑ᴵ y → (a ⊕ x) ⊑ᴵ (a ⊕ y)
⊕-path : ∀ a {x y} → x <ᴵ y → (a ⊕ x) <ᴵ (a ⊕ y)
⊕-≅ : ∀ a {x y} → x ≅ᴵ y → (a ⊕ x) ≅ᴵ (a ⊕ y)
<⊕ : ∀ a y {c} → c <ᴵ a → c <ᴵ (a ⊕ y)
a ⊕ zero = a
a ⊕ suc b = suc (a ⊕ b)
a ⊕ lim f s = lim (λ n → a ⊕ f n) (λ n → ⊕-mono a (s n))
⊕-mono a {y = y} z⊑ = Sim→⊑ᴵ (<⊕ a y)
⊕-mono a (s⊑ e q) = s⊑ (⊕-≅ a e) (⊕-path a q)
⊕-mono a (l⊑ h) = l⊑ (λ n → ⊕-mono a (h n))
⊕-path a zero = zero
⊕-path a (suc q) = suc (⊕-path a q)
⊕-path a (lim n q) = lim n (⊕-path a q)
⊕-≅ a z≅ = ≅ᴵ-refl a
⊕-≅ a (s≅ d) = s≅ (⊕-≅ a d)
⊕-≅ a (l≅ h) = l≅ (λ n → ⊕-≅ a (h n))
<⊕ a zero q = q
<⊕ a (suc y) q = suc (<⊕ a y q)
<⊕ a (lim f s) q = lim 0 (<⊕ a (f 0) q)

𝟏 : Ordᴵ
𝟏 = suc zero

⊕-≺ : ∀ a {x y} → x ≺ᴵ y → (a ⊕ x) ≺ᴵ (a ⊕ y)
⊕-≺ a (via e q) = via (⊕-≅ a e) (⊕-path a q)

SV-1⊕ : ∀ {a} → SV a → SV (𝟏 ⊕ a)
SV-1⊕ svz = svs svz
SV-1⊕ (svs d) = svs (SV-1⊕ d)
SV-1⊕ (svl d st) = svl (λ n → SV-1⊕ (d n))
  (λ n → let c , r , k = st n in 𝟏 ⊕ c , ⊕-≺ 𝟏 r , ⊕-mono 𝟏 k)

Pos-1⊕ : ∀ a → Pos (𝟏 ⊕ a)
Pos-1⊕ zero = ps
Pos-1⊕ (suc a) = ps
Pos-1⊕ (lim f s) = pl

f≼ : ∀ a → forget a ≼ forget (𝟏 ⊕ a)
f≼ zero = z≼
f≼ (suc a) = s≼s (f≼ a)
f≼ (lim f s) = l≼ (λ n → ≼l n (f≼ (f n)))

f⊕≼ : ∀ a → forget (𝟏 ⊕ a) ≼ suc (forget a)
f⊕≼ zero = s≼s z≼
f⊕≼ (suc a) = s≼s (f⊕≼ a)
f⊕≼ (lim f s) = l≼ (λ n → ≼-trans (f⊕≼ (f n)) (s≼s (≼l n (≼-refl _))))

emb1 : ∀ {x x′} → x ≅ᴵ x′ → PEmb x (𝟏 ⊕ x′)
emb1 e = record
  { map = λ {c} _ → 𝟏 ⊕ c
  ; bnd = λ r → ⊕-≺ 𝟏 (≺ᴵ-respʳ r e)
  ; mono = λ r s w → ⊕-≺ 𝟏 w
  ; coh = λ r s w → ⊕-≅ 𝟏 w }
```

## §3 链

```agda
Ix-⊞ : ∀ {a b ℓ m} → Ix a ℓ → Ix b m → Ix (a ⊞ b) (ℓ ⊕ m)
Ix-⊞ ia iz = ia
Ix-⊞ ia (is ib) = is (Ix-⊞ ia ib)
Ix-⊞ ia (il h) = il (λ n → Ix-⊞ ia (h n))

fr≅ : ∀ {a b : Ord₀} → a FL.≅ b → fr a ≅ fr b
fr≅ FL.z≅ = z≅
fr≅ (FL.s≅ e) = s≅ (fr≅ e)
fr≅ (FL.l≅ h) = l≅ (λ n → fr≅ (h n))
fr≅ (FL.lᵢ≅ {p = ()} e h)
fr≅ (FL.upˡ {r = ()} e)
fr≅ (FL.upʳ {r = ()} e)

⊴-fr : ∀ {a b : Ord₀} → a ⊴₀ b → fr a ⊑ fr b
⊴-fr (r0 e) = ≅→⊑ (fr≅ e)
⊴-fr (s0 d) c = ≺s (⊴-fr d c)
⊴-fr (l0 n d) c = ≺l n (⊴-fr d c)

HS-fr : ∀ (y : Ord₀) → Lit₀ y → HS (fr y)
HS-fr FL.zero u = hz
HS-fr (FL.suc a) u = hs (HS-fr a u)
HS-fr (FL.lim f) (st , u) = hl (λ n → HS-fr (f n) (u n)) (λ n → ⊴-fr (st n))
HS-fr (FL.limᵢ () f) u
HS-fr (FL.up () x) u

γ-≺ : ∀ m → N.γ m ≺ N.γ (suc m)
γ-≺ zero = ≺l 0 (≺l 2 (≺z (≅-refl⁰ _)))
γ-≺ (suc m) = Ψ⁰-mono (s⊑′ (toLevel-≺ (N.cert m) (N.cert (suc m)) (γ-≺ m))) (Fstep (N.L m))

module Run (y : ℕ → Ord₀) (ly : ∀ n → Lit₀ (y n)) (vs : ℕ → A) (t : ∀ n → vs n ≈ᴬ one ⊞ rd (y n))
  (E₀ : fr (y 0) ≅ N.γ 1)
  (Eh : ∀ n ℓ → Ix (vs n) ℓ → (p : zero <ᴵ ℓ) → fr (y (suc n)) ≅ ψ⁰ (Ω ℓ)) where

  z : ℕ → Ordᶜ zero
  z n = fr (y n)

  hz′ : ∀ n → HS (z n)
  hz′ n = HS-fr (y n) (ly n)

  lv : ℕ → Ordᴵ
  lv n = toLevel (z n) (hz′ n)

  a : ℕ → Ordᴵ
  a n = 𝟏 ⊕ lv n

  ix : ∀ n → Ix (vs n) (a n)
  ix n = Ix-≈ (t n) (Ix-⊞ (is iz) (Ix-rd (y n) (hz′ n)))

  St-z : ∀ n → St (z n)
  SV-lv : ∀ n → SV (lv n)
  SV-a : ∀ n → SV (a n)
  e-z : ∀ n → z (suc n) ≅ Fʸ (a n)

  e-z n = Eh n (a n) (ix n) (z<SV (SV-a n) (Pos-1⊕ (lv n)))
  St-z zero = St-≅ E₀ (St-F (SV-L 0) (pos-L 0))
  St-z (suc n) = St-≅ (e-z n) (St-F (SV-a n) (Pos-1⊕ (lv n)))
  SV-lv n = SV-toLevel (z n) (hz′ n) (St-z n)
  SV-a n = SV-1⊕ (SV-lv n)

  HSF : ∀ n → HS (Fʸ (a n))
  HSF n = HS-≅ (≅-sym (e-z n)) (hz′ (suc n))
```

## §4 交错

```agda
  up-g : ℕ → ℕ
  up-g zero = 1
  up-g (suc k) = suc (suc (suc (up-g k)))

  upp : ∀ k → z k ≼ N.γ (up-g k)
  upp zero = ≅→≼ E₀
  upp (suc k) =
    ≼-trans (≅→≼ (e-z k))
      (Cross (SV-a k) (SV-L (suc (up-g k)))
        (≼-trans (f⊕≼ (lv k))
          (≼-trans (s≼s (≼-trans (≅→≼ (forget-toLevel (z k) (hz′ k))) (upp k)))
            (≼-trans (≺→s≼ (γ-≺ (up-g k))) (≅→≼ (≅-sym (forget-toLevel (N.γ (suc (up-g k))) (N.cert (suc (up-g k)))))))))
        (N.cert (suc (suc (up-g k)))))

  lw-g : ℕ → ℕ
  lw-g zero = 0
  lw-g (suc k) = suc (suc (lw-g k))

  lw : ∀ k → N.γ (suc k) ≼ z (lw-g k)
  lw zero = ≅→≼ (≅-sym E₀)
  lw (suc k) =
    ≼-trans (Cross (SV-L (suc k)) (SV-a j)
              (≼-trans (≅→≼ (forget-toLevel (N.γ (suc k)) (N.cert (suc k))))
                (≼-trans (lw k) (≼-trans (≅→≼ (≅-sym (forget-toLevel (z j) (hz′ j)))) (f≼ (lv j)))))
              (HSF j))
      (≼-trans (Ψ-emb (emb1 (toLevel-≅ (HSF j) (hz′ (suc j)) (≅-sym (e-z j)))))
               (≅→≼ (≅-sym (e-z (suc j)))))
    where j = lw-g k

  T : Ordᶜ zero
  T = lim z

  T≈ : T ≈ᵛ BTBOᴵ
  T≈ = l≼ (λ n → ≼l (up-g n) (≼-trans (upp n) (γ-step (up-g n)))) , l≼ (λ k → ≼l (lw-g k) (lw k))
```

## §5 `TᵖΩ`

```agda
any-certᵖ : (d : G (Tᴰ 1 azero one g₀ (z⊲ one))) → fr (force d) ≈ᵛ BTBOᴵ
any-certᵖ (gw (gc G₀ vs gv up₁ Gh t₀ tS s₀ sS)) = K.T≈
  where
  yy : ℕ → Ord₀
  yy = outs (force G₀) (λ k → force (Gh k))
  ly : ∀ n → Lit₀ (yy n)
  ly zero = Lit-force G₀
  ly (suc n) = Lit-force (Gh n)
  tt′ : ∀ n → vs n ≈ᴬ one ⊞ rd (yy n)
  tt′ zero = t₀
  tt′ (suc n) = tS n
  E₀ : fr (force G₀) ≅ N.γ 1
  E₀ = ≅-trans (fr≅ (force-Y C.self (Ω̇ 0 one) g₀ g₀ _ _ _ _ (Q-Ω one) G₀)) (term 0)
  Eh : ∀ n ℓ → Ix (vs n) ℓ → (p : zero <ᴵ ℓ) → fr (force (Gh n)) ≅ ψ⁰ (Ω ℓ)
  Eh n ℓ ix p = ≅-trans (fr≅ (force-Y C.self _ (gv n) (gv n) _ _ _ (lgw (gv n)) (qw (Q-Ω (vs n))) (Gh n))) (Y-sim (lgw (gv n)) ix p)
  module K = Run yy ly vs tt′ E₀ Eh

TᵖΩ : Ord₀
TᵖΩ = Tᵖ 1 azero one g₀ (z⊲ one)

TᵖΩ≈ : fr TᵖΩ ≈ᵛ BTBOᴵ
TᵖΩ≈ = any-certᵖ (G-Tᵖ 1 azero one g₀ (z⊲ one))

TᵖΩ≈T⁰ : fr TᵖΩ ≈ᵛ fr T⁰
TᵖΩ≈T⁰ = ≼-trans (proj₁ TᵖΩ≈) (≅→≼ (≅-sym T⁰≅)) , ≼-trans (≅→≼ T⁰≅) (proj₂ TᵖΩ≈)
```
