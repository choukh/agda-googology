# 高度坐标的共享槽 (四): 坐标类型随级变的一族 (`K₁` 的 `κHc`)

> 不含记号. 入口 [Slot](Slot.lagda.md). 只读导入否定一路的 [NegSlotPre](NegSlotPre.lagda.md) (`K1.no-forgetK₁`, `K1.no-forget-jx`; 那一篇写在接口定稿之前, 不依赖 `SlotIf`), 不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 原卡点 ([RsOwn](RsOwn.lagda.md) 判断 2): `κH f = κHc (jx f)`, 坐标 `HB (Lev (jx f))`, 类型随 $f$ 变.
>
> - **`kH-Dg` (定理, 必要条件).** 任一带证据的世界 `subW K₁ P` 上, 对一切 `κHc c` 一致的 `RsK` 族给出对角解码 `Dg H₀ (λ c → HB (Lev c))`: 一族映射 `HB (Lev c) → HB (Lev c′)`, 对角上恒等. 只对 `κH f` 一族也一样 (`kHjx-Dg`).
> - **`no-slotKH`, `no-slotJx` (定理, 否定).** 接口形状的共享槽 (`Slot`, 读回精确) 加上 [SlotGen](SlotGen.lagda.md) 的一起升, 对 `κHc` 一族 (下标取遍 `H₀`) 或只对 `κH f` 一族 (下标取遍 `ℕ → H₀`) 都**不存在**, 只要共享种类上有一个 `RsK` 与一个世界. 证明: `Gen` 的一起升是 "忘" 的 (`SlotGen.rs-other`: 升成员 $j$ 到 $v$ 之后, 成员 $j'$ 的顶是 $\mathrm{cE}^{-}_{j'}(\mathrm{cE}_j\,v)$, 只依赖 $v$), 而族里同时有高一级的成员 (`κHc (hs c)`, 或 `κH (f⁺ f)`), 撞否定一路的 `no-forgetK₁`, `no-forget-jx`. 证据世界不需要另给: `wset` 写出的世界自带证据 (`al-set`).
>
> **只否定什么.** 只否定: 读回精确的 `Slot` 与**这一种**一起升 (`Gen`: 先在共享槽里升, 再把一切成员的共享世界置成同一个) 对**含相邻两级成员**的一族. **不否定**: 不忘的升界 (高一级成员的新界依赖旧世界); 读回有损的槽 (只对像精确); 只含同一级拷贝的族 ([SlotCp](SlotCp.lagda.md), [SlotTw](SlotTw.lagda.md) 的构造就是这一类); 不经共享槽的别的升界形状. 路线状态: `κHc` 上 "经共享槽一起升" 的这一形状被定理否定; `κHc` 上的升界问题本身仍开着 (`kH-Dg` 说任何形状都要一个对角解码).
>
> **更正 (否定一路后来的定理, 已复核: 从仓库根编译 `NegSlotWall`, 退出码 0).** 否定一路的 [NegSlotWall](NegSlotWall.lagda.md) 有更强的 **`no-slot-κHc : ¬ Slot K₁ tp₁ H₀ κHc Q tq κ₀`**, 不需要 `RsK`, 世界或任何升界: `SL.slot-ret` 说任一 `Slot` 的两个可达成员的坐标类型互为收缩, 相邻两级撞 `no-desc-step`. 所以对 `Slot` 形状, 上面 "不否定: 不忘的升界" 不再成立: `κHc` 一族连 `Slot` 记录本身都没有, 与用哪种升界无关. `no-slotKH`, `no-slotJx` 仍然成立, 只是前提多于需要. "不否定" 里其余几条 (读回有损, 只含同一级拷贝的族, 不经共享槽的升界) 不变. `no-slot-pair` (族含相邻两级, 高的那份有 `RsK`) 与 `no-slot-κH` (`κH f` 一族) 也在那里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SlotKH where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.GenFoldIf using (TopG; top; tpK; w₀; K₁)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NegGenFoldUpd using (jx)
open import OCF.Align.RsOwnIf using (RsK; subW; topSub)
open import OCF.Align.SlotIf
open import OCF.Align.SlotGen using (module Gen; rsFam→Dg)
import OCF.Align.NegSlotPre as NS
```

## §1 必要条件: 对角解码

```agda
kH-Dg : ∀ {P : Wd K₁ → Set} → RsFam (subW K₁ P) (topSub tp₁) H₀ κHc → Σ (Wd K₁) P → Dg H₀ (λ c → HB (Lev c))
kH-Dg R w = rsFam→Dg R w

kHjx-Dg : ∀ {P : Wd K₁ → Set} → RsFam (subW K₁ P) (topSub tp₁) (ℕ → H₀) (λ f → κHc (jx f)) → Σ (Wd K₁) P →
          Dg (ℕ → H₀) (λ f → HB (Lev (jx f)))
kHjx-Dg R w = rsFam→Dg R w
```

## §2 接口形状的共享槽对 `κHc` 一族不存在

```agda
module _ {Q : KS} {tq : TopG Q} {κ₀ : K Q} where
  no-slotKH : Slot K₁ tp₁ H₀ κHc Q tq κ₀ → RsK Q tq κ₀ → Wd Q → ⊥
  no-slotKH S R₀ ω = K1.no-forgetK₁ hz (rsS hz) (rsS (hs hz)) w0 fg
    where
    open Gen S R₀
    module K1 = NS.K1 (ShW S)
    w0 : Σ (Wd K₁) (ShW S)
    w0 = wset S ω (w₀ (genKc 1)) , (ω , al-set S ω (w₀ (genKc 1)))
    fg : K1.ForgetK hz (rsS hz)
    fg w w′ v = trans (rs-other hz (hs hz) (proj₁ w) (proj₂ w) v) (sym (rs-other hz (hs hz) (proj₁ w′) (proj₂ w′) v))

  -- 只服务 κH f 一族 (下标 ℕ → H₀) 也一样
  no-slotJx : Slot K₁ tp₁ (ℕ → H₀) (λ f → κHc (jx f)) Q tq κ₀ → RsK Q tq κ₀ → Wd Q → ⊥
  no-slotJx S R₀ ω = K1.no-forget-jx f₀ (rsS f₀) (rsS (K1.f⁺ f₀)) w0 fg
    where
    open Gen S R₀
    module K1 = NS.K1 (ShW S)
    f₀ : ℕ → H₀
    f₀ _ = hz
    w0 : Σ (Wd K₁) (ShW S)
    w0 = wset S ω (w₀ (genKc 1)) , (ω , al-set S ω (w₀ (genKc 1)))
    fg : ∀ w w′ v → top (topSub tp₁) (K1.κH (K1.f⁺ f₀)) (RsK.rs (rsS f₀) w v)
                  ≡ top (topSub tp₁) (K1.κH (K1.f⁺ f₀)) (RsK.rs (rsS f₀) w′ v)
    fg w w′ v = trans (rs-other f₀ (K1.f⁺ f₀) (proj₁ w) (proj₂ w) v) (sym (rs-other f₀ (K1.f⁺ f₀) (proj₁ w′) (proj₂ w′) v))
```

## §3 前提可满足

`no-slotKH` 的另两个前提有实例: 共享种类上的 `RsK` (例如 [SlotCp](SlotCp.lagda.md) 的 `rsNew a′`, 在 `Q = Lev (hs a′)` 上) 与 `Q` 的一个世界 (`w₀ (genLev (hs a′))`). 被否定的是 `Slot` 这一个前提 (对 `κHc` 一族). 同一个 `Slot` 记录对**同一级的拷贝族**有实例 (`SlotCp.Cp.cpSlot`, `SlotTw.slotU`), 所以接口本身不是空的.

## §4 结论 (按档)

- **[定理]** `kH-Dg`, `kHjx-Dg` (必要条件).
- **[定理, 否定]** **`no-slotKH`**, **`no-slotJx`** (依据否定一路 `NegSlotPre.K1.no-forgetK₁`, `no-forget-jx` 与本路 `SlotGen.rs-other`).
- **[判断]** 区别在 "族里有没有相邻两级的成员". 拷贝族 (`SlotTw.famU`) 的成员都是同一个种类的拷贝, 坐标类型化到同一个, 没有一份比另一份高一级, 一起升 "忘" 不要紧. `κHc` 一族里 `κHc c` 与 `κHc (hs c)` 相邻, 高的那份的坐标类型里有低的那份的整个高度类型; 一起升若让高的那份的新界只看 $v$, 就要把高一级的高度膨胀地压进低一级 (`NegSlotPre.no-inflate`).
- **[判断]** `κHc` 上剩下的形状 (未构造, 未否定): (i) 不忘: 高一级成员的新界依赖旧世界, 例如只在 "旧界 $\lhd$ 搬运后的 $v$" 时才动它 (这又要比较两级的值, 未写); (ii) 一族只取同一级: 例如只对 `κHc c` 的某个子族, 其中没有 $c$ 与 $\mathrm{hs}\,c$ 同在 (`jx` 一族里 $f$ 与 $f^+$ 同在, 所以不行); (iii) 换塔: 让需要回灌的深种类都是拷贝 (`StratTwTw` 的分量里拷贝与非拷贝都有, `SlotTw` 只覆盖拷贝).
