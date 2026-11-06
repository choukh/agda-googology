# 按级回灌, 否定一路 (七): 对构造一路实例 `KindLvTw` 的检查

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 只读导入构造一路的 [KindLvTw](KindLvTw.lagda.md) (18:49 之后的版本: 塔是 `NewTwr` 的塔的式子, 写在 `module NT₁` 里, 每站求值走 `KindLvEv.evK`/`ρK` (经 `KindLvRun` 加平凡 `lv`); 最终坍缩是按级回灌的 `ColL GΛ LdΛ flΛ Λ lΛ one⊲ lvΛ`; 本篇用到的名字 `κ₁`, `K1`, `lvΛ`, `NT₁.Bᴧ` 两版都有), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 问题 (任务原话): "它的回灌是否真的到了每个种类的级". 结论 (定理):
>
> 1. **只有一个种类有级回灌** (`only-κ₁`): `lvΛ κ = inj₁ L` 推出 $\kappa\equiv$ `κ₁ = (1 , (inj₂ 2 , inj₂ tt))`. 别的种类一律退回 `GΛ` 的 `fbA` (`KindLvRun` 的 `RKv`).
> 2. **这个种类确实在最终层里** (`κ₁-occ`, `refl`): 层号对角的第 1 项是 `Bᴧ 0 ⊞ hs (hΩ κ₁ g)`. 所以按级回灌的那一行在坍缩里不是空的 (前提可满足).
> 3. **它的级层就是它自己的级** (`K1-own`, `lv-κ₁`, `Lev-agree`, `refl`): `ℓ K1 = lyL 1`, 读回是 `readL 1`, 坐标 `HB (Lev 1)`; 种类在自己的分量 `Lev 2` 里的级 (`NegKindLvLev.lvK`) 也是 $1$ (在 `HB S₀` 里), 两个 "1" 在不同的类型里, `Lev` 定义相等 (有限数字的 `Lev` 不看种类结构). 这一致是因为级是不含函数的有限数字.
> 4. **第 $s+2$ 站的头种类 (坐标 `HB (Lev B_{s+1})`) 没有回灌** (`head-lossy`, `head-lossy-fb`, `refl`): `lvΛ` 给 `inj₂ tt`, 退回的 `fbA GΛ` 也是 `inj₂ tt`. 第 1 站读回分量里除 `κ₁` 外的种类同 (`NegNewTwrFeed.lossyΛ`).
> 5. **起始世界里 `κ₁` 的界是 $0$** (`start-κ₁`, `refl`): 坍缩从基世界 `(w₀ GΛ , hz)` 起步 (`ColL.W₁`).
>
> **对照分离子.** `K1` 的 `rs` 是 "升一份留别份" (下标 `inj₂ c` 上, `c` 是 $2$ 时换, 否则不动), 它不撞 [NegKindLvUpd](NegKindLvUpd.lagda.md) 是因为下标 $2$ 是不含函数的闭项, 按模式判定 (`isTwo`). 第 $s+2$ 站的头种类的下标 $B_{s+1}$ 含求值的函数分支; 对含函数的下标族 (`jx f`, `hs (jx f)`), 一致的 "升 + 留" 推出分离子 (`updH₁-sep`, `updHΛ⁺-sep`). 判断: 把 `K1` 的写法推广到后面的站, 撞的是这一条, 不是工程问题.
>
> **只否定什么.** 只说 `KindLvTw` 这一实例的形状 (哪些种类有级回灌, 起始世界), 不说 `TK` 的值 (没有 `ord` 的比较), 不否定按级回灌这条路线, 也不否定构造一路未走通的互递归塔 (那是编译失败, 不是否定定理).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (fbA; tpK; top; w₀)
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.NewTwrColl using (GΛ)
open import OCF.Align.KindLvIf using (KLv; ℓ; lyL)
open import OCF.Align.KindLvTw using (κ₁; K1; lvΛ; module NT₁)
open import OCF.Align.NegKindLvLev using (lvK)
open import Relation.Nullary using (¬_)
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.NegGenFoldUpd using (jx; Sep; sep→WLPO)
open import OCF.Align.NegNewTwrFeed using (ext₁)
open import OCF.Align.NegKindLvUpd using (κH; PtUpdH₁; updH₁-sep)
```

## §1 只有一个种类有级回灌

```agda
only-κ₁ : ∀ κ (L : KLv KΛc (tpK GΛ) _ κ) → lvΛ κ ≡ inj₁ L → κ ≡ κ₁
only-κ₁ (suc zero , (inj₂ (hs (hs hz)) , inj₂ tt)) L e = refl
only-κ₁ (zero , _) L ()
only-κ₁ (suc (suc s) , _) L ()
only-κ₁ (suc zero , (inj₁ tt , κ)) L ()
only-κ₁ (suc zero , (inj₂ hz , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs hz) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hs hz)) , inj₁ κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hs (hs c))) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hs (hl f))) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hs (hΩ κ′ g))) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hl f)) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hs (hΩ κ′ g)) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hl f) , κ)) L ()
only-κ₁ (suc zero , (inj₂ (hΩ κ′ g) , κ)) L ()
```

## §2 `κ₁` 在最终层里

```agda
κ₁-occ : Σ (E KΛc κ₁ → HB KΛc) (λ g → NT₁.Bᴧ 1 ≡ NT₁.Bᴧ 0 ⊞ hs (hΩ κ₁ g))
κ₁-occ = _ , refl
```

## §3 它的级层就是它自己的级

```agda
K1-own : ℓ K1 ≡ lyL {KΛc} (hs hz)
K1-own = refl

lv-κ₁ : lvK {S₀} (hs (hs hz)) (inj₂ tt) ≡ inj₂ (hs hz)
lv-κ₁ = refl

Lev-agree : Lev {KΛc} (hs hz) ≡ Lev {S₀} (hs hz)
Lev-agree = refl

E-κ₁ : E KΛc κ₁ ≡ HB (Lev {KΛc} (hs hz))
E-κ₁ = refl
```

## §4 后面各站的头种类没有回灌

```agda
-- 第 s+2 站的层号 B (s+1) 的头是后继 (NewTwrK.B-suc), 头种类是分量 hs c 的新种类
head-lossy : ∀ s (c : HB (Kc (suc s))) → lvΛ (suc (suc s) , (inj₂ (hs c) , inj₂ tt)) ≡ inj₂ tt
head-lossy s c = refl

head-lossy-fb : ∀ s (c : HB (Kc (suc s))) → fbA GΛ (suc (suc s) , (inj₂ (hs c) , inj₂ tt)) ≡ inj₂ tt
head-lossy-fb s c = refl
```

## §5 起始世界

```agda
start-κ₁ : top (tpK GΛ) κ₁ (w₀ GΛ) ≡ hz
start-κ₁ = refl
```

## §6 把 `K1` 的 `rs` 推广到含函数的下标: 分离子

`K1` 的 `rs` 在 `KΛc` 的第 1 站, 下标 `inj₂ 2` 上 "升新种类的界, 留别的分量". 同一个形状对第 1 站下标族 `hs (jx f)` 的头种类 `(1 , κH f)` 一致地做 (升到 $1$ 以上 + 留), 推出分离子 (经 `ext₁` 归到 `NegKindLvUpd.updH₁-sep`).

```agda
record PtUpdHΛ : Set where
  field
    updH   : Wd KΛc → (ℕ → H₀) → Wd KΛc
    raiseH : ∀ w f → Bd KΛc (1 , κH f) (hs hz) (updH w f)
    keepH  : ∀ w f f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd KΛc (1 , κH f′) c (updH w f) → Bd KΛc (1 , κH f′) c w

toH₁Λ : PtUpdHΛ → PtUpdH₁
toH₁Λ P = record
  { updH = λ w f → updH (ext₁ w) f 1
  ; raiseH = λ w f → raiseH (ext₁ w) f
  ; keepH = λ w f f′ ne b → keepH (ext₁ w) f f′ ne b }
  where open PtUpdHΛ P

updHΛ-sep : PtUpdHΛ → Sep
updHΛ-sep P = updH₁-sep (toH₁Λ P)

updHΛ→WLPO : FE₀ → PtUpdHΛ → WLPO
updHΛ→WLPO fe P = sep→WLPO fe (updHΛ-sep P)
```

前提的两半各自可满足: 与 `NegKindLvUpd` 的 `half₁R`/`half₁K` 相同 (在第 1 个分量上用 `upOne₁`, 或不动); 在可判定的闭下标 $2$ 上两半同时成立就是 `K1` 的 `rs` (`KindLvTw.up₂`).

## §7 结论 (按档)

- **[定理, 否定]** **`updHΛ-sep`** (`KΛc` 第 1 站, 含函数的下标族上 "升 + 留" ⇒ 分离子); **[条件 `FE₀`]** `updHΛ→WLPO`.
- **[定理]** `only-κ₁`, `κ₁-occ`, `K1-own`, `lv-κ₁`, `Lev-agree`, `E-κ₁`, `head-lossy`, `head-lossy-fb`, `start-κ₁`.
- **[判断]** 按级回灌在 `KindLvTw` 里到了一个种类 (第 1 站读回分量的头, 级 $1$); 到 "每个种类的级" 没有. 与 `NewTwr.TN` 的差只在这一个种类的闭包结点 (第 0 层目标下从有损换成按级 $1$ 的读回 `readL 1`). 值: 没有定理; 读法 (判断) 不应高于 GenFold/NewTwr 一档以上 (级 $1$ 的读回与 `rd₂` 同型, `KindLvRd` 文件头).
