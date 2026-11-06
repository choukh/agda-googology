# UIP 条件下的回灌 (一): 可入下标上的升界链, 有界的新节点格

> 不含记号. 入口 [UipFb](UipFb.lagda.md). 接 [AdmWCoh](AdmWCoh.lagda.md) 的 `raise₀ᴮ` (只升 $c_0$ 本身的更新, 四条律无条件) 与 `uip→raise₀-coh` (保 `Coh≡`, 条件: `UIPᴴ`). 最小实例 `Slot` ([AdmWIf](AdmWIf.lagda.md) §2): 外层世界 $(a,b)$, 每个可入坐标 $(c,p)$ ($p : c\lhd_{[a]}b$) 一个分量, 是 `step (G₀ c)` 的世界; 新种类 $(c,\text{new})$ 的坐标是 `HB (G₀ c)`, 界是分量的第二项 (槽).
>
> 三件事:
>
> 1. **一步 (无条件).** `yes-cell`: 在任一可入 $(c_0,p_0)$ 处用 `raise₀` 接上 $\delta$, 格 "旧槽 $\boxplus\,\delta$" 在新世界里有界, 对一切 $\delta$. 在后继坐标 $c_0=c+1$ 处取 $\delta=\Omega_{\mathrm{top}}(G_0\,c)$ (新种类的 $\Omega$-节点, `new-Ωtop`): 含新种类节点的格有界 (`yes-Ω-cell`). $c=0$ 时坐标类型是 `HB S₁` (`E-κ₂`, `refl`), 格正是 `ChainZNeg.no-Ω-cell` 的格 $y\boxplus\Omega_{\mathrm{top}}S_0$; $c=1$ 时坐标类型是 `HB (step S₁)` (`E-κ₃`), 第二级.
> 2. **可达世界 (`ReachR`).** 由合法且相干的起点经任意多次 `raise₀` (任意可入坐标, 任意合法增量) 得到. 合法: 无条件 (`reach-lg`). 相干: **条件 `RC`** (`reach-coh`), `RC` = "`raise₀` 保 `Coh≡`" (`RaiseCoh Coh≡ raise₀ᴮ`), 由 `UIPᴴ` 推出 (`uip→RC`, 即 `AdmWCoh.uip→raise₀-coh`). 坐标比较: 同一条件 (`reach-cmp`, 经 `AdmWCoh.coh≡→cmpK`). 相干与比较只经过 `RC`, 不直接用 `UIPᴴ`. **`no-chain` 的结论在这一族里不成立** (`¬noChainᴿ`, 无条件): 对一切可达世界与一切可入的后继坐标, "含新节点的格从不有界" 是假的.
> 3. **升界链 (`Chain`).** 对照 `HtTowerFFold.κc₁` 的三步: 读界 (槽 $x_n$), 升界 ($x_{n+1}=x_n\boxplus\delta(x_n)$, 经 `raise₀`), 低层搬回 (别的坐标不动, `chain-off`; 外层世界是模块参数, 链上不变). 读回 $\delta$ 是模块参数. 定理: 每一格合法 (`chain-lg`), 槽的递推 (`chain-at`), 槽的 ℕ-极限是合法高度 (`lΛᶜ`), 第 $n+1$ 个世界里格 $x_n\boxplus\delta(x_n)$ 有界 (`chain-cell`); 条件 `RC` (于是 `UIPᴴ`): 每个世界相干 (`chain-coh`), 坐标可比 (`chain-cmp`).
>
> **范围.** `yes-cell` 与 `¬noChainᴿ` 只说 `raise₀` 生成的世界; 它们不说任何折叠用到了这些格. 它们与 `no-chain` 不矛盾: 那里的世界族是 `growL′` 从 `dW 1` 生成的 (统一增量, 裸积), 这里是 `raise₀` 在 `Slot` 上生成的 (选择性增量, 可入下标).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K. `UIPᴴ` 只作模块参数 (前提可满足: `AdmWUip.fe→uip`, 条件: Funext), 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UipFbChain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (raise₀; raise₀ᴮ; at₀; off₀; mono₀; legal₀; UIPᴴ; uip→raise₀-coh; coh≡→cmpK)
open import OCF.Align.DiagK3One using (NoNew)
open Slot
open RaiseIf using (RaiseCoh)

-- 本路用到的相干前提: raise₀ 保 Coh≡. UIPᴴ 是它的一个充分条件 (AdmWCoh.uip→raise₀-coh)
RC : Set
RC = RaiseCoh Coh≡ raise₀ᴮ

uip→RC : UIPᴴ → RC
uip→RC = uip→raise₀-coh
```

## §1 一步: 升界后的格有界

```agda
yes-cell : ∀ w lo v c₀ (p₀ : AdmE w c₀) δ →
  Bdᴮ (c₀ , inj₂ tt) (proj₂ (v c₀ p₀) ⊞ δ) (w , raise₀ w lo v c₀ p₀ δ)
yes-cell w lo v c₀ p₀ δ =
  p₀ , subst (λ X → (proj₂ (v c₀ p₀) ⊞ δ) ⊲[ proj₁ X ] proj₂ X) (sym (at₀ w lo v c₀ p₀ δ)) hself

-- 新种类的 Ω-节点
new-Ωtop : ∀ S → ¬ NoNew (Ωtop S)
new-Ωtop S ()

-- 后继坐标处的坐标类型就是 step (G₀ c)
G₀-hs : ∀ c → G₀ (hs c) ≡ step (G₀ c)
G₀-hs c = refl

E-κ₂ : Eᴮ (hs hz , inj₂ tt) ≡ HB (step S₀)
E-κ₂ = refl

E-κ₃ : Eᴮ (hs (hs hz) , inj₂ tt) ≡ HB (step (step S₀))
E-κ₃ = refl

yes-Ω-cell : ∀ w lo v c (p : AdmE w (hs c)) →
  Bdᴮ (hs c , inj₂ tt) (proj₂ (v (hs c) p) ⊞ Ωtop (G₀ c)) (w , raise₀ w lo v (hs c) p (Ωtop (G₀ c)))
yes-Ω-cell w lo v c p = yes-cell w lo v (hs c) p (Ωtop (G₀ c))
```

## §2 可达世界

```agda
module Reach (w : Out) (lo : LgO w) where
  data ReachR : Cmp w → Set where
    r0 : ∀ {v} → LgWᴮ (w , v) → Coh≡ (w , v) → ReachR v
    rg : ∀ {v} → ReachR v → ∀ c₀ (p₀ : AdmE w c₀) δ → LgB δ → ReachR (raise₀ w lo v c₀ p₀ δ)

  reach-lg : ∀ {v} → ReachR v → LgWᴮ (w , v)
  reach-lg (r0 l c) = l
  reach-lg (rg r c₀ p₀ δ lδ) = legal₀ w lo _ c₀ p₀ δ lδ (reach-lg r)

  -- no-chain 的结论的同形物, 对 raise₀ 生成的世界族
  NoChainᴿ : HB S₀ → Set
  NoChainᴿ c = ∀ {v} → ReachR v → (p : AdmE w (hs c)) → ∀ y δ → ¬ NoNew δ →
               ¬ Bdᴮ (hs c , inj₂ tt) (y ⊞ δ) (w , v)

  ¬noChainᴿ : ∀ {v} → ReachR v → ∀ c → AdmE w (hs c) → ¬ NoChainᴿ c
  ¬noChainᴿ {v} r c p nc =
    nc (rg r (hs c) p (Ωtop (G₀ c)) (Lg-Ωtop (G₀ c))) p (proj₂ (v (hs c) p)) (Ωtop (G₀ c)) (new-Ωtop (G₀ c))
       (yes-Ω-cell w lo v c p)

  -- 条件: RC (于是 UIPᴴ)
  module _ (rc : RC) where
    reach-coh : ∀ {v} → ReachR v → Coh≡ (w , v)
    reach-coh (r0 l c) = c
    reach-coh (rg r c₀ p₀ δ lδ) = rc w lo _ c₀ p₀ δ lδ (reach-coh r)

    reach-cmp : ∀ {v} → ReachR v → ∀ {k x x′} → Bdᴮ k x (w , v) → Bdᴮ k x′ (w , v) →
                Prᴮ k (w , v) x′ x ⊎ Prᴮ k (w , v) x x′
    reach-cmp r bx bx′ =
      coh≡→cmpK (step S₀) (inj₂ tt) (λ c → step (G₀ c)) bx bx′ (reach-lg r) (reach-coh r)
```

## §3 升界链

模块参数: 外层世界 $w$ 与合法性, 起点 $v_0$ (合法), 可入坐标 $(c_0,p_0)$, 读回 $\delta$ (把当前槽读成一个合法增量). 链的每一格带着合法性, 读回要它.

```agda
module Chain (w : Out) (lo : LgO w) (v₀ : Cmp w) (lv₀ : LgWᴮ (w , v₀))
  (c₀ : HB S₀) (p₀ : AdmE w c₀)
  (δ⋆ : (h : HB (G₀ c₀)) → LgB h → HB (G₀ c₀)) (lδ⋆ : ∀ h lh → LgB (δ⋆ h lh)) where

  Stt : Set
  Stt = Σ (Cmp w) (λ v → LgWᴮ (w , v))

  -- 读界
  slotS : Stt → HB (G₀ c₀)
  slotS s = proj₂ (proj₁ s c₀ p₀)

  lslotS : (s : Stt) → LgB (slotS s)
  lslotS s = proj₂ (proj₂ (proj₂ s) c₀ p₀)

  δS : Stt → HB (G₀ c₀)
  δS s = δ⋆ (slotS s) (lslotS s)

  -- 升界 (只升 c₀ 的一切拷贝)
  next : Stt → Stt
  next s = raise₀ w lo (proj₁ s) c₀ p₀ (δS s) ,
           legal₀ w lo (proj₁ s) c₀ p₀ (δS s) (lδ⋆ (slotS s) (lslotS s)) (proj₂ s)

  chain : ℕ → Stt
  chain zero = v₀ , lv₀
  chain (suc n) = next (chain n)

  V : ℕ → Cmp w
  V n = proj₁ (chain n)

  x : ℕ → HB (G₀ c₀)
  x n = slotS (chain n)

  δ : ℕ → HB (G₀ c₀)
  δ n = δS (chain n)

  chain-lg : ∀ n → LgWᴮ (w , V n)
  chain-lg n = proj₂ (chain n)

  lx : ∀ n → LgB (x n)
  lx n = lslotS (chain n)

  -- 槽的递推
  chain-at : ∀ n → x (suc n) ≡ x n ⊞ δ n
  chain-at n = cong proj₂ (at₀ w lo (V n) c₀ p₀ (δ n))

  -- 低层搬回: 别的可入坐标不动; 外层世界本来就不变
  chain-off : ∀ n c (p : AdmE w c) → ¬ (c₀ ≡ c) → V n c p ≡ v₀ c p
  chain-off zero c p ne = refl
  chain-off (suc n) c p ne = trans (off₀ w lo (V n) c₀ p₀ (δ n) c p ne) (chain-off n c p ne)

  chain-≤ : ∀ n → (w , V n) ≤ᴮ (w , V (suc n))
  chain-≤ n = mono₀ w lo (V n) c₀ p₀ (δ n) (lδ⋆ (x n) (lx n))

  -- 第 n+1 个世界里, 格 x n ⊞ δ n 有界
  chain-cell : ∀ n → Bdᴮ (c₀ , inj₂ tt) (x n ⊞ δ n) (w , V (suc n))
  chain-cell n = yes-cell w lo (V n) c₀ p₀ (δ n)

  -- 槽的 ℕ-极限
  x-st : ∀ {u} n → x n ⊲[ u ] x (suc n)
  x-st {u} n = subst (λ z → x n ⊲[ u ] z) (sym (chain-at n)) (⊞-fst (x n) (δ n))

  Λᶜ : HB (G₀ c₀)
  Λᶜ = hl x

  lΛᶜ : LgB Λᶜ
  lΛᶜ = x-st , lx

  -- 条件: RC (于是 UIPᴴ)
  module _ (rc : RC) (coh₀ : Coh≡ (w , v₀)) where
    chain-coh : ∀ n → Coh≡ (w , V n)
    chain-coh zero = coh₀
    chain-coh (suc n) = rc w lo (V n) c₀ p₀ (δ n) (lδ⋆ (x n) (lx n)) (chain-coh n)

    chain-cmp : ∀ n {k y y′} → Bdᴮ k y (w , V n) → Bdᴮ k y′ (w , V n) →
                Prᴮ k (w , V n) y′ y ⊎ Prᴮ k (w , V n) y y′
    chain-cmp n by by′ =
      coh≡→cmpK (step S₀) (inj₂ tt) (λ c → step (G₀ c)) by by′ (chain-lg n) (chain-coh n)
```
