# 族增量世界上的真折叠 (一): 一级 (κ₂) 的折叠

> 不含记号. 入口 [FamFold](FamFold.lagda.md), 接口 [FamFoldIf](FamFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **折叠.** `F.fold w lo p₀ v Λ W`: 外层世界 $w$, 坐标 $1$ 的可入证据 $p_0$, 族增量世界的分量函数 $v$, 层 $\Lambda$ : `HB S₂` ↦ 两种种类第 2 层的数据树 (`D₂ W`). 对 $\Lambda$ 结构递归:
>
> - $0$, 后继, ℕ-极限: `n0`, `⨾ n1`, `nl` (与 `toD₁` 同法).
> - 旧种类 `κA` (坐标 `A`) 的 $\Omega$-节点: 闭包 `nκ`, 坐标 $c$ 上的分支是 $g(c)$ 的折叠 (世界的 `A` 分量升到 $c$).
> - 旧种类 `κH` (坐标 `H₀`) 的 $\Omega$-节点: 闭包 `nμ`, 更大的世界 $W'$ 上的分支是 $g(W'\text{ 的高度界})$ 的折叠 (与 `Ωd` 的 `nμ` 一行同法).
> - **新种类 κ₂ (坐标 `HB S₁`) 的 $\Omega$-节点 $\mathrm{h\Omega}\,\kappa_2\,g$: 回灌.** 世界链 $v_0=v$, $v_{n+1}$ = `rFC` ($v_n$ 在 $(1,p_0)$ 处的族更新, 连 `hs 1` 分量里的拷贝一起升; `LocUipFeed.raiseFCᴮ`), 增量是族 `famRd (rdO o)`, 其中 $o$ = **折叠自己**在分支 $g(\text{槽}_n)$ 上的输出 ($\text{槽}_n$ = $v_n$ 在 $(1,p_0)$ 的槽). 节点折成 $n\mapsto$ (第 $n$ 个世界里分支 $g(\text{槽}_n)$ 的折叠) 的 ℕ-极限.
>
> **读回** `rdO o = δ⋆ (rd₂ 0 o)`: 先把输出 $o$ 读成两种种类的层 $h$ (`rd₂`), 再用两种种类的折叠折 $\Omega_{2\boxplus h}$, 取第 2 层目标上的输出, 读回 `HB S₁` (`UipFbClosed.δ⋆`, 即 `HtTowerNFb.Fb₂` 的读回, 底取 $1$). 所以每一步的增量是 "整条折叠 (这一级 + 两种种类) 在分支上的第 2 层输出". 合法由形状给出 (`Lg-rd₂`).
>
> **读回对坐标一致** (`famO`): 族 `famRd x c = cast c x`, `cast` 只按坐标的构造子定义 (不看 $p_0$, 不判定任何相等), `cast 1 x = x` 定义相等. 范围: 有限坐标给嵌入, 极限坐标给 $0$; 一切级 (极限的 $c_0$) 不由它处理.
>
> **闭项.** `idx Λ = rd₂ 0 (fold … Λ)`: 一级折叠把 `HB S₂` 的层折成两种种类的层; `T₃ Λ = T⁺ (idx Λ)`. 合法与 FGH 都由形状给出, 不用 $\Lambda$ 的合法性 (κ₂ 一级不做任何坐标比较). 级顶 `Tᵀ = T₃ (Ωtop S₁)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop; nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; κA; κH; n0; n1; _⨾_; nl; nκ; nμ)
open import OCF.Align.HtTowerNRead using (D₂; rd₂; rdp₂; rd₂-fst; Lg-rd₂)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord; Ω₂ᴴ; W₁)
open import OCF.Align.DiagK3Zero using (_≈_; ≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.DiagK3One using (NoNew; up-noNew)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (fin)
open import OCF.Align.LocUipIf using (Inc; RaiseF; raiseF; atF; belowF; monoF; legalF; cohF; CopyCoh)
open import OCF.Align.LocUipFeed using (rFC; raiseFCᴮ; copyFC)
open import OCF.Align.UipFbClosed using (w₂; lo₂; p₁; vz; lgvz; cohvz; δ⋆; lδ⋆; noNew-≈)
open import OCF.Align.FamFoldIf
open Slot
```

## §1 读回与它的族

```agda
-- 只按坐标的构造子: 1 处恒等, 更高的有限坐标处嵌入, 别处 0
cast : (c : HB S₀) → Ht → HB (G₀ c)
cast hz x = hz
cast (hs hz) x = x
cast (hs (hs c)) x = up (cast (hs c) x)
cast (hs (hl f)) x = hz
cast (hs (hΩ κ g)) x = hz
cast (hl f) x = hz
cast (hΩ κ g) x = hz

famRd : Ht → Inc
famRd x c = cast c x

famRd-at : ∀ x → famRd x c₁ ≡ x
famRd-at x = refl

-- 输出读成两种种类的层
lay : Out₂ → Ht
lay o = rd₂ (tt , tt) hz (o W₁)

Lg-lay : ∀ o → LgB (lay o)
Lg-lay o = Lg-rd₂ (tt , tt) hz (o W₁) tt

-- 读回: 两种种类折叠 Ω_{2 ⊞ lay o} 的第 2 层输出, 读回 HB S₁ (底 1)
rdO : Out₂ → Ht
rdO o = δ⋆ (lay o) (Lg-lay o)

lg-rdO : ∀ o → LgB (rdO o)
lg-rdO o = lδ⋆ (lay o) (Lg-lay o)

famO : Uniform Out₂ c₁ rdO
famO = (λ o → famRd (rdO o)) , (λ o → refl)

-- LocUipNegSec 的前提: 读回值是族的值
sec₁ : ∀ o → SecAt c₁ (rdO o)
sec₁ o = famRd (rdO o) , refl
```

## §2 折叠

```agda
module F (w : Out) (lo : LgO w) (p₀ : AdmE w c₁) where
  slot : Cmp w → Ht
  slot u = slotAt u c₁ p₀

  -- 世界链: 每步族更新 (连拷贝), 增量是 Fo 在当前世界上的输出的读回
  ch : (Cmp w → Out₂) → Cmp w → ℕ → Cmp w
  ch Fo v zero = v
  ch Fo v (suc n) = rFC w lo (ch Fo v n) c₁ p₀ (famRd (rdO (Fo (ch Fo v n))))

  fold : Cmp w → HB S₂ → Out₂
  fold v hz W = n0
  fold v (hs x) W = fold v x W ⨾ n1
  fold v (hl f) W = nl (λ n → fold v (f n) W)
  fold v (hΩ (inj₁ (inj₁ tt)) g) W = nκ tt (λ {c} _ _ → fold v (g c) (c , proj₂ W))
  fold v (hΩ (inj₁ (inj₂ tt)) g) W = nμ tt (λ {W′} _ _ → fold v (g (proj₂ W′)) W′)
  fold v (hΩ (inj₂ tt) g) W =
    nl (λ n → fold (ch (λ u → fold u (g (slot u))) v n) (g (slot (ch (λ u → fold u (g (slot u))) v n))) W)

  -- κ₂ 节点处的链: 分支在当前槽处的折叠
  chain : Cmp w → (Ht → HB S₂) → ℕ → Cmp w
  chain v g = ch (λ u → fold u (g (slot u))) v

  -- 链的律
  ch-lg′ : ∀ v g → LgWᴮ (w , v) → ∀ n → LgWᴮ (w , chain v g n)
  ch-lg′ v g lW zero = lW
  ch-lg′ v g lW (suc n) =
    legalF raiseFCᴮ w lo (chain v g n) c₁ p₀ _ (lg-rdO (fold (chain v g n) (g (slot (chain v g n))))) (ch-lg′ v g lW n)

  ch-coh′ : ∀ v g → CohC (w , v) → ∀ n → CohC (w , chain v g n)
  ch-coh′ v g cc zero = cc
  ch-coh′ v g cc (suc n) =
    cohF raiseFCᴮ w lo (chain v g n) c₁ p₀ _ (proj₁ (ch-coh′ v g cc n)) ,
    copyFC w lo (chain v g n) c₁ p₀ _ (proj₂ (ch-coh′ v g cc n))

  ch-≤′ : ∀ v g n → (w , chain v g n) ≤ᴮ (w , chain v g (suc n))
  ch-≤′ v g n = monoF raiseFCᴮ w lo (chain v g n) c₁ p₀ _

  -- 槽的递推: 新槽 = 旧槽 ⊞ 读回 (在同一个证据 p₀ 上)
  slot-s : ∀ v g n → slot (chain v g (suc n)) ≡ slot (chain v g n) ⊞ rdO (fold (chain v g n) (g (slot (chain v g n))))
  slot-s v g n = cong proj₂ (atF raiseFCᴮ w lo (chain v g n) c₁ p₀ _)

  -- 新槽有界: 链上第 n+1 个世界里, (1, 槽) 种类之下
  slot-bd : ∀ v g n → Bdᴮ (c₁ , inj₂ tt) (slot (chain v g n)) (w , chain v g n)
  slot-bd v g n = p₀ , hself
```

## §3 接口的实例

```agda
feed₁ : Feed₁ raiseFCᴮ
feed₁ = record
  { fold   = λ w lo p₀ → F.fold w lo p₀
  ; rdO    = rdO
  ; lg-rdO = lg-rdO
  ; famO   = famO
  ; chain  = λ w lo p₀ → F.chain w lo p₀
  ; ch-z   = λ w lo p₀ v g → refl
  ; ch-s   = λ w lo p₀ v g n → refl
  ; fold-Ω = λ w lo p₀ v g W → refl
  ; ch-lg  = λ w lo p₀ → F.ch-lg′ w lo p₀
  ; ch-coh = λ w lo p₀ → F.ch-coh′ w lo p₀
  ; ch-≤   = λ w lo p₀ → F.ch-≤′ w lo p₀
  }
```

## §4 闭项

外层世界 $(0,2)$ (`UipFbClosed.w₂`, 证据唯一), 坐标 $1$ 的证据 `p₁`, 分量全 $0$ (`vz`, 合法, 两种相干都是 `refl`).

```agda
copyvz : CopyCoh (w₂ , vz w₂)
copyvz c₀ q₀ q₁ = refl

cohC₀ : CohC (w₂ , vz w₂)
cohC₀ = cohvz w₂ , copyvz

module F₂ = F w₂ lo₂ p₁

idx : Input₁
idx Λ = lay (F₂.fold (vz w₂) Λ)

Lg-idx : ∀ Λ → LgB (idx Λ)
Lg-idx Λ = Lg-lay (F₂.fold (vz w₂) Λ)

T₃ : Fold₁
T₃ Λ _ = T⁺ (idx Λ) (Lg-idx Λ)

Lg-T₃ : ∀ Λ (l : LgB Λ) → Lg (T₃ Λ l)
Lg-T₃ Λ l = Lg-T⁺ (idx Λ) (Lg-idx Λ)

-- 级顶
Tᵀ : A
Tᵀ = T₃ (Ωtop S₁) (Lg-Ωtop S₁)

Lg-Tᵀ : Lg Tᵀ
Lg-Tᵀ = Lg-T₃ (Ωtop S₁) (Lg-Ωtop S₁)

fghᵀ : ℕ → ℕ
fghᵀ = FL.FGH (ord Tᵀ)

-- 级顶之上: Ω₃ + 1, Ω₃ · 2, Ω₃² (新种类上 x ↦ Ω₃ · x, 对坐标递归, 连续)
Ω₃ : HB S₂
Ω₃ = Ωtop S₁

Ω₃+1 Ω₃·2 Ω₃² : HB S₂
Ω₃+1 = hs Ω₃
Ω₃·2 = Ω₃ ⊞ Ω₃
Ω₃² = hΩ κ₂ (nbᴮ hz (λ x h → h ⊞ Ω₃))

Lg-Ω₃² : LgB Ω₃²
Lg-Ω₃² = cont→Lg (nb-contB tt (λ x h → ⊞-fst h Ω₃) (λ x h lh → Lg-⊞ h Ω₃ lh (Lg-Ωtop S₁)))

Tᵀ+1 Tᵀ·2 Tᵀ² : A
Tᵀ+1 = T₃ Ω₃+1 (Lg-Ωtop S₁)
Tᵀ·2 = T₃ Ω₃·2 (Lg-⊞ Ω₃ Ω₃ (Lg-Ωtop S₁) (Lg-Ωtop S₁))
Tᵀ² = T₃ Ω₃² Lg-Ω₃²

fghᵀ² : ℕ → ℕ
fghᵀ² = FL.FGH (ord Tᵀ²)
```

## §5 级顶不被压回

级顶的输入是链上格的 ℕ-极限 (`top-hl`, `refl`); 第 2 格的最外是 `κH` 的 $\Omega$-节点 (`cell₂-ΩH`, 对具体项的计算), 所以含新种类节点 (`cell₂-new`). 由此: 输入不与 `Ω₂ᴴ` 互模拟 (构造子不同), 不与任何 `H₀` 嵌入互模拟 (嵌入不含新种类节点, 互模拟保持这一点).

```agda
pieces : ℕ → D₂ W₁
pieces n = F₂.fold (F₂.chain (vz w₂) up n) (up (F₂.slot (F₂.chain (vz w₂) up n))) W₁

cells : ℕ → Ht
cells = rdp₂ (tt , tt) hz pieces

top-hl : idx (Ωtop S₁) ≡ hl cells
top-hl = refl

isΩH₁ : Ht → Set
isΩH₁ (hΩ (inj₂ tt) _) = ⊤
isΩH₁ _ = ⊥

cell₂-ΩH : isΩH₁ (cells 2)
cell₂-ΩH = tt

cell₂-new : ¬ NoNew (cells 2)
cell₂-new ()

¬top≈Ω₂ : ¬ (idx (Ωtop S₁) ≈ Ω₂ᴴ)
¬top≈Ω₂ ()

¬top≈up : ∀ (h : H₀) → ¬ (idx (Ωtop S₁) ≈ up h)
¬top≈up (hl f) (≈l e) = cell₂-new (noNew-≈ (e 2) (up-noNew (f 2)))

notPressed : NotPressed idx
notPressed = ¬top≈Ω₂ , ¬top≈up

-- 连同合法性 (接口的 NotPressed 不含合法性; 只换采样投影也能满足它, 否定一路 notPressed-e₊)
notPressedᴸ : (∀ Λ → LgB (idx Λ)) × NotPressed idx
notPressedᴸ = Lg-idx , notPressed

-- 世界侧: 链上第 1 个世界的槽 (κ₂ 的界) 含新种类节点, 在世界里有界, 世界合法且两种相干
slot₁-new : ¬ NoNew (F₂.slot (F₂.chain (vz w₂) up 1))
slot₁-new ()

slot₁-bd : Bdᴮ (c₁ , inj₂ tt) (F₂.slot (F₂.chain (vz w₂) up 1)) (w₂ , F₂.chain (vz w₂) up 1)
slot₁-bd = F₂.slot-bd (vz w₂) up 1

chain-lg : ∀ n → LgWᴮ (w₂ , F₂.chain (vz w₂) up n)
chain-lg = F₂.ch-lg′ (vz w₂) up (lgvz w₂ lo₂)

chain-coh : ∀ n → CohC (w₂ , F₂.chain (vz w₂) up n)
chain-coh = F₂.ch-coh′ (vz w₂) up cohC₀

-- 格在第一位置序里逐个变大 (结构, 不是序数值)
cells-st : ∀ n {w′} → cells n ⊲[ w′ ] cells (suc n)
cells-st n = rd₂-fst (tt , tt) (cells n) (pieces n)
```
