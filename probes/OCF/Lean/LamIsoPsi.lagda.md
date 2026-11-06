# LamIso (一): $\hat\Omega^m$ 的翻译 `Ψ` (提供者沿坐标选, 前缀逐项继承)

> 不含记号. 入口 [LamIso](LamIso.lagda.md), 接口 [LamIsoIf](LamIsoIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 对一切种类结构 `T` (模块参数), 目标是层的种类结构 `X = step T`.
>
> **要做的事.** 站的层号 `st (2+n) = ofHB (tw (2+n))`, 而 `tw (2+n)` 的第 $c$ 支是 $\hat\Omega^n(1\boxplus c)$ (`tw-eq`). 要在 `HB X` 里写一个层与它忠实同形 (`Prt`), 就要把 $\hat\Omega^m(A\boxplus \iota_k\,y)$ 翻译进 `X`. 对 $y$ 递归 (同 $\hat\Omega$ 的定义):
>
> - $y=0$: 前缀 $b$ (已翻译的 $\hat\Omega^m A$).
> - $y=y'+1$, $m=m'+1$: $\hat\Omega^{m'+1}(Z+1) = \hat\Omega^{m'}(\Omega_Z)$, $Z=A\boxplus\iota_k\,y'$. 新结点的种类是**提供者** `Pv` 的新种类 (坐标 `HB (Lv (ofHB Z))`), 第 $e$ 支是 $\Psi_{m'}$ 以 $\Psi_m(y')$ 为前缀、在 $e$ 上的翻译. 前缀 $\Psi_m(y')$ 对一切 $e$ 是**同一个项** (逐项继承; 否定一路 `NegLamIsoPre.path-illegal` 划出的 "按路径换分量" 不出现).
> - $y$ 的 $\mathbb N$-极限、$\Omega$-结点 (`Lv k` 的种类, 经嵌入 `E` 的拷贝): 逐支.
>
> **提供者沿坐标选** (`Src m A k`): 对每个坐标 $y$ 一个嵌入 `Emb (Lv (ofHB (Ω̂^m (Z_y+1)))) X`; 它的左分量是 `FL (ofHB Z_y)` (新结点的种类), 右分量 `inj₂ (e+1)` 是下一层的提供者. 提供者只依赖坐标 (即依赖被翻译的层号), 不依赖在层里的路径.
>
> **迭代与三条等式.** `it m Z` = $\hat\Omega$ 在外面迭代 $m$ 次 (与 `tw` 同一个递归). `eqS`, `eqL`, `eqΩ` 对 $m$ 归纳, 每一步是 `cong Ω̂`, 不用函数外延. 对具体的 $m$ 它们化成 `refl`, 所以经它们 `subst` 出来的同形与提供者在具体的站上计算.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.LeanTBase
module OCF.Lean.LamIsoPsi (T : KS) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanLvIf using (Emb; j; cv; vc; cv-vc; π; lgπ; bd→; bd←; pr→)
open import OCF.Lean.LeanLvEmb using (idE; stepE; supE; _∘E_)
open import OCF.Lean.LamIsoIf

X : KS
X = step T
```

## §1 迭代 $\hat\Omega$ 与三条等式

```agda
it : ℕ → HB SL → HB SL
it zero Z = Z
it (suc m) Z = Ω̂ (it m Z)

eqS : ∀ m Z → it (suc m) Z ≡ it m (Ω̂ Z)
eqS zero Z = refl
eqS (suc m) Z = cong Ω̂ (eqS m Z)

eqL : ∀ m (f : ℕ → HB SL) → it m (hl f) ≡ hl (λ n → it m (f n))
eqL zero f = refl
eqL (suc m) f = cong Ω̂ (eqL m f)

eqΩ : ∀ m κ (g : E SL κ → HB SL) → it m (hΩ κ g) ≡ hΩ κ (λ c → it m (g c))
eqΩ zero κ g = refl
eqΩ (suc m) κ g = cong Ω̂ (eqΩ m κ g)

Zf : HB SL → (k : LH) → HB (Lv k) → HB SL
Zf A k y = A ⊞ ι k (up y)

eqH : ∀ m Z → it (suc m) (hs Z) ≡ hΩ (νL (ofHB Z)) (λ e → it m (Ω̂ Z ⊞ ι (ofHB Z) (up e)))
eqH m Z = trans (eqS m (hs Z)) (eqΩ m (νL (ofHB Z)) (λ e → Ω̂ Z ⊞ ι (ofHB Z) (up e)))

-- lΩ 的左右分量
ΩF : (k : LH) → (HB (Lv k) → LH) → ⊤ ⊎ HB (Lv k) → KS
ΩF k g = [ (λ _ → step (Lv k)) , (λ c → Lv (g c)) ]′

lft : ∀ k g → Emb (FL k) (Lv (lΩ k g))
lft k g = supE {⊤ ⊎ HB (Lv k)} {ΩF k g} (inj₁ tt)

rgt : ∀ k g c → Emb (Lv (g c)) (Lv (lΩ k g))
rgt k g c = supE {⊤ ⊎ HB (Lv k)} {ΩF k g} (inj₂ c)
```

## §2 拷贝结点的忠实同形 (`node` 的递归)

种类 $\kappa$ : `K (Lv k)` 经嵌入 `E` 放进 `X`; `ofHB` 把这样的结点经 `node` 降到它的级. 对 $k,\kappa$ 递归, 每一步把嵌入复合上对应的分量; 到达新种类时就是 `pΩ`.

```agda
prtNode : ∀ k (κ : K (Lv k)) (E₀ : Emb (Lv k) X) {h : E (Lv k) κ → LH} {br : E X (j E₀ κ) → HB X} →
          (∀ e → Prt T (br e) (h (cv E₀ e))) → Prt T (hΩ (j E₀ κ) br) (node k κ h)
prtNode lz (() , _) E₀ σ
prtNode (ls x) (inj₁ κ) E₀ σ = prtNode x κ (E₀ ∘E stepE) σ
prtNode (ls x) (inj₂ tt) E₀ σ = pΩ E₀ σ (λ _ → inj₂ tt)
prtNode (ll f) (n , κ) E₀ σ = prtNode (f n) κ (E₀ ∘E supE {ℕ} {λ i → Lv (f i)} n) σ
prtNode (lΩ k g) (inj₁ tt , inj₁ κ) E₀ σ = prtNode k κ (E₀ ∘E lft k g ∘E stepE) σ
prtNode (lΩ k g) (inj₁ tt , inj₂ tt) E₀ σ = pΩ (E₀ ∘E lft k g) σ (λ _ → inj₂ tt)
prtNode (lΩ k g) (inj₂ c , κ) E₀ σ = prtNode (g c) κ (E₀ ∘E rgt k g c) σ
```

## §3 提供者与翻译 `Ψ`

```agda
Src : ℕ → HB SL → LH → Set
Src m A k = (y : HB (Lv k)) → Emb (Lv (ofHB (it m (hs (Zf A k y))))) X

module _ {m A k} (Q : Src (suc m) A k) (y : HB (Lv k)) where
  Gb : HB (Lv (ofHB (Zf A k y))) → LH
  Gb e = ofHB (it m (Ω̂ (Zf A k y) ⊞ ι (ofHB (Zf A k y)) (up e)))

  Qt : Emb (Lv (lΩ (ofHB (Zf A k y)) Gb)) X
  Qt = subst (λ H → Emb (Lv (ofHB H)) X) (eqH m (Zf A k y)) (Q y)

  Pv : Emb (FL (ofHB (Zf A k y))) X
  Pv = Qt ∘E lft (ofHB (Zf A k y)) Gb

  Qn : Src m (Ω̂ (Zf A k y)) (ofHB (Zf A k y))
  Qn e = Qt ∘E rgt (ofHB (Zf A k y)) Gb (hs e)

Ψ : ∀ m {A k} → HB X → Src m A k → Emb (Lv k) X → HB (Lv k) → HB X
Ψ m b Q E₀ hz = b
Ψ m b Q E₀ (hl f) = hl (λ n → Ψ m b Q E₀ (f n))
Ψ m b Q E₀ (hΩ κ g) = hΩ (j E₀ κ) (λ e → Ψ m b Q E₀ (g (cv E₀ e)))
Ψ zero b Q E₀ (hs y) = hs (Ψ zero b Q E₀ y)
Ψ (suc m) b Q E₀ (hs y) =
  hΩ (j (Pv Q y) (inj₂ tt)) (λ e → Ψ m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) (cv (Pv Q y) {inj₂ tt} e))
```

## §4 前缀是第一位置, 单调, 合法由形状给出

```agda
Ψ-fst : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) y {w} → b ⊲[ w ] Ψ m b Q E₀ y
Ψ-fst m b Q E₀ hz = hself
Ψ-fst m b Q E₀ (hl f) = hlim 0 (Ψ-fst m b Q E₀ (f 0))
Ψ-fst m b Q E₀ (hΩ κ g) {w} = hLim (botBd X (j E₀ κ) w) (Ψ-fst m b Q E₀ (g (cv E₀ (bot X (j E₀ κ)))))
Ψ-fst zero b Q E₀ (hs y) = hsuc (Ψ-fst zero b Q E₀ y)
Ψ-fst (suc m) b Q E₀ (hs y) {w} =
  hLim (botBd X (j (Pv Q y) (inj₂ tt)) w)
    (⊲ᴮ-tr (Ψ-fst (suc m) b Q E₀ y) (Ψ-fst m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) _))

Ψ-step : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) y {w} → Ψ m b Q E₀ y ⊲[ w ] Ψ m b Q E₀ (hs y)
Ψ-step zero b Q E₀ y = hsuc hself
Ψ-step (suc m) b Q E₀ y {w} =
  hLim (botBd X (j (Pv Q y) (inj₂ tt)) w) (Ψ-fst m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) _)

Ψ-mono : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) {y y′ w} → y ⊲[ π E₀ w ] y′ → Ψ m b Q E₀ y ⊲[ w ] Ψ m b Q E₀ y′
Ψ-mono m b Q E₀ hself = hself
Ψ-mono m b Q E₀ (hsuc p) = ⊲ᴮ-tr (Ψ-mono m b Q E₀ p) (Ψ-step m b Q E₀ _)
Ψ-mono m b Q E₀ (hlim n p) = hlim n (Ψ-mono m b Q E₀ p)
Ψ-mono m b Q E₀ {y} {w = w} (hLim {g = g} {c = c} bd p) =
  hLim (bd← E₀ bd) (subst (λ z → Ψ m b Q E₀ y ⊲[ w ] Ψ m b Q E₀ (g z)) (sym (cv-vc E₀ c)) (Ψ-mono m b Q E₀ p))

Lg-Ψ : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) → LgB b → ∀ y → LgB y → LgB (Ψ m b Q E₀ y)
Lg-Ψ m b Q E₀ lb hz _ = lb
Lg-Ψ m b Q E₀ lb (hl f) (st′ , l) = (λ n → Ψ-mono m b Q E₀ (st′ n)) , (λ n → Lg-Ψ m b Q E₀ lb (f n) (l n))
Lg-Ψ m b Q E₀ lb (hΩ κ g) (mo , l) =
  (λ lw e e′ p → Ψ-mono m b Q E₀ (mo (lgπ E₀ lw) (bd→ E₀ e) (bd→ E₀ e′) (pr→ E₀ p))) ,
  (λ {w} {c} lw e → Lg-Ψ m b Q E₀ lb (g (cv E₀ c)) (l (lgπ E₀ lw) (bd→ E₀ e)))
Lg-Ψ zero b Q E₀ lb (hs y) l = Lg-Ψ zero b Q E₀ lb y l
Lg-Ψ (suc m) b Q E₀ lb (hs y) l =
  (λ lw e e′ p → Ψ-mono m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) (pr→ (Pv Q y) p)) ,
  (λ {w} {c} lw e → Lg-Ψ m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) (Lg-Ψ (suc m) b Q E₀ lb y l) (cv (Pv Q y) c)
     (lgB⊲ (bd→ (Pv Q y) e) (proj₁ (lgπ (Pv Q y) lw)) (proj₂ (lgπ (Pv Q y) lw))))
```

## §5 忠实同形

前缀与 $\hat\Omega^m A$ 忠实同形, 则 $\Psi_m(y)$ 与 $\hat\Omega^m(A\boxplus\iota_k\,y)$ 忠实同形. 新结点的第 $e$ 支带后继种类 (`succE`, 对一切 $m$; $m=0$ 时同 `LeanLvTmS.σ₂⁺`: 第 $e+1$ 支的层号字面是第 $e$ 支的后继). $y$ 的 $\mathbb N$-极限与拷贝结点处不带 (`inj₂ tt`).

**后继种类的嵌入** `succE m Y`: `Lv (ofHB (Ω̂^m (Y+1)))` 里有 `step (Lv (ofHB (Ω̂^m Y)))` 的一份 (对 $m$ 递归: $m=0$ 时就是它自己; $m+1$ 时在 $\Omega_Y$ 的第 $1$ 支, 那里是 $\hat\Omega^m(\hat\Omega Y+1)$, 再用 `eqS`). 于是一切 $\hat\Omega$-结点的第 $e$ 支 (层号 $\hat\Omega^m(\cdots\boxplus e)$) 在第 $e+1$ 支里找到后继种类, 对一切 $m$.

```agda
succE : ∀ m Y → Emb (step (Lv (ofHB (it m Y)))) (Lv (ofHB (it m (hs Y))))
succE zero Y = idE
succE (suc m) Y =
  subst (λ H → Emb (step (Lv (ofHB (it (suc m) Y)))) (Lv (ofHB H))) (sym (eqH m Y))
    (subst (λ H → Emb (step (Lv (ofHB H))) (Lv (lΩ (ofHB Y) (λ e → ofHB (it m (Ω̂ Y ⊞ ι (ofHB Y) (up e)))))))
       (sym (eqS m Y))
       (rgt (ofHB Y) (λ e → ofHB (it m (Ω̂ Y ⊞ ι (ofHB Y) (up e)))) (hs hz) ∘E succE m (Ω̂ Y)))

P⟨_⟩ : HB X → HB SL → Set
P⟨ a ⟩ H = Prt T a (ofHB H)

Prt-Ψ : ∀ m {A k} b (Q : Src m A k) (E₀ : Emb (Lv k) X) y → P⟨ b ⟩ (it m A) → P⟨ Ψ m b Q E₀ y ⟩ (it m (Zf A k y))
Prt-Ψ m b Q E₀ hz σ = σ
Prt-Ψ m {A} {k} b Q E₀ (hl f) σ =
  subst (λ H → P⟨ Ψ m b Q E₀ (hl f) ⟩ H) (sym (eqL m (λ n → Zf A k (f n))))
    (pl (λ n → Prt-Ψ m b Q E₀ (f n) σ) (λ _ → inj₂ tt))
Prt-Ψ m {A} {k} b Q E₀ (hΩ κ g) σ =
  subst (λ H → P⟨ Ψ m b Q E₀ (hΩ κ g) ⟩ H) (sym (eqΩ m (k , inj₁ κ) (λ c → Zf A k (g c))))
    (prtNode k κ E₀ (λ e → Prt-Ψ m b Q E₀ (g (cv E₀ e)) σ))
Prt-Ψ zero b Q E₀ (hs y) σ = ps (Prt-Ψ zero b Q E₀ y σ)
Prt-Ψ (suc m) {A} {k} b Q E₀ (hs y) σ =
  subst (λ H → P⟨ Ψ (suc m) b Q E₀ (hs y) ⟩ H) (sym (eqH m (Zf A k y)))
    (pΩ (Pv Q y)
       (λ e → Prt-Ψ m (Ψ (suc m) b Q E₀ y) (Qn Q y) (Pv Q y ∘E stepE) (cv (Pv Q y) e)
                (subst (λ H → P⟨ Ψ (suc m) b Q E₀ y ⟩ H) (eqS m (Zf A k y)) (Prt-Ψ (suc m) b Q E₀ y σ)))
       (λ e → inj₁ (rgt (ofHB (Zf A k y)) (Gb Q y) (hs (cv (Pv Q y) {inj₂ tt} e)) ∘E
                    succE m (Ω̂ (Zf A k y) ⊞ ι (ofHB (Zf A k y)) (up (cv (Pv Q y) {inj₂ tt} e))))))
```
