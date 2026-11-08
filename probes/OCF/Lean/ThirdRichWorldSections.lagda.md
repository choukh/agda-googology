# Third 的整族世界扩张：界、坐标与合法值覆盖同时给出

原默认世界把每个组件塔的界设为零。本篇在原 `Sb/Tw` 上，以一族
真正同类型的输入树同时扩张各处的界；不按组件编号查找，不比较裸下标。
每个新坐标由旧界加本轮富合法化得到，新界是其后继。因此旧世界可嵌入、
新坐标合法且可入，原输入的合法坐标值被它覆盖，三件事分别证明。

这不是完整折叠：**尚未从原 Φ/ΦX 的单次输出产生这样一个全目标族**。
下面有原全族地板的实际实例，不能用它替代动态反馈的这一义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichWorldSections where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; fl; topT)
open import OCF.Lean.ThirdLeg using (wT)
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.ThirdRichLegValueRun as Raw
import OCF.Lean.ThirdRichLegValueLegal as Val

Rf : KS → Set
Rf S = ∀ w → _≤w_ S w w

rfT : ∀ U → Rf U → ∀ m → Rf (Tw U m)
rfT U r hz w = r w
rfT U r (hs m) (w , b) = rfT U r m w , hself
rfT U r (hl f) w = λ n → rfT U r (f n) (w n)
rfT U r (hΩ κ g) w = λ e → rfT U r (g e) (w e)

rfS : ∀ n → Rf (Sb n)
rfS zero w = tt
rfS (suc n) w (inj₁ _) = rfS n (proj₁ (w (inj₁ tt))) , hself
rfS (suc n) w (inj₂ c) = rfT (Sb n) (rfS n) (hs c) (w (inj₂ c))

module Frames (n : ℕ) (u : Wd (Sb n)) (lu : LgW (Sb n) u) where
  U = Sb n
  Section : Set
  Section = (m : HB U) → HB (Tw U m)

  world : Section → (m : HB U) → Wd (Tw U m)
  world B hz = u
  world B (hs m) = world B m , B m
  world B (hl f) = λ i → world B (f i)
  world B (hΩ κ g) = λ e → world B (g e)

  world-legal : ∀ B → (∀ m → LgB (B m)) → ∀ m → LgW (Tw U m) (world B m)
  world-legal B lB hz = lu
  world-legal B lB (hs m) = world-legal B lB m , lB m
  world-legal B lB (hl f) = λ i → world-legal B lB (f i)
  world-legal B lB (hΩ κ g) = λ e → world-legal B lB (g e)

  feedback : Section → Section → Section
  feedback B Q m = B m ⊞ Rich.legT n m (Q m)

  next : Section → Section → Section
  next B Q m = hs (feedback B Q m)

  feedback-legal : ∀ B → (∀ m → LgB (B m)) → ∀ Q m → LgB (feedback B Q m)
  feedback-legal B lB Q m = Lg-⊞ _ _ (lB m) (Rich.Lg-legT n m (Q m))

  grow : ∀ B Q m → _≤w_ (Tw U m) (world B m) (world (next B Q) m)
  grow B Q hz = rfS n u
  grow B Q (hs m) = grow B Q m , hsuc (⊞-fst (B m) (Rich.legT n m (Q m)))
  grow B Q (hl f) = λ i → grow B Q (f i)
  grow B Q (hΩ κ g) = λ e → grow B Q (g e)

  admitted : ∀ B Q m → Bd (Tw U (hs m)) (inj₂ tt) (feedback B Q m) (world (next B Q) (hs m))
  admitted B Q m = hsuc hself

  covers : ∀ B Q m → Val.Domain.Cover (Tw U m) (Raw.LegalT n m) (Q m) (feedback B Q m)
  covers B Q m = Val.Domain.ct (Val.inflateT n m (Q m))
    (Val.Domain.right (Tw U m) (Raw.LegalT n m) (B m) (Rich.legT n m (Q m)))

  -- 全组件的实际世界；指标分量单列，不要求它等于塔零高度的界。
  full : HB U → Section → Wd (Sb (suc n))
  full i B (inj₁ _) = u , i
  full i B (inj₂ c) = world B (hs c)

  full-legal : ∀ i → LgB i → ∀ B → (∀ m → LgB (B m)) → LgW (Sb (suc n)) (full i B)
  full-legal i li B lB (inj₁ _) = lu , li
  full-legal i li B lB (inj₂ c) = world-legal B lB (hs c)

  full-grow : ∀ i B Q → _≤w_ (Sb (suc n)) (full i B) (full i (next B Q))
  full-grow i B Q (inj₁ _) = rfS n u , hself
  full-grow i B Q (inj₂ c) = grow B Q (hs c)

  from-default : ∀ B Q m → _≤w_ (Tw U m) (wT U u m) (world (next B Q) m)
  from-default B Q hz = rfS n u
  from-default B Q (hs m) = from-default B Q m , z⊲ᴮ (next B Q m)
  from-default B Q (hl f) = λ i → from-default B Q (f i)
  from-default B Q (hΩ κ g) = λ e → from-default B Q (g e)

  full-admitted : ∀ i B Q c → Bd (Sb (suc n)) (inj₂ c , inj₂ tt)
    (feedback B Q c) (full i (next B Q))
  full-admitted i B Q c = admitted B Q c

  -- 实填：对原 Third 的全部地板输入作同一操作，不另造假设族。
  floors : Section
  floors m = topT U (fl n) m

  initial : Section
  initial m = hz

  advanced-world : HB U → Wd (Sb (suc n))
  advanced-world i = full i (next initial floors)

  advanced-legal : ∀ i → LgB i → LgW (Sb (suc n)) (advanced-world i)
  advanced-legal i li = full-legal i li (next initial floors)
    (λ m → feedback-legal initial (λ _ → tt) floors m)

  floors-covered : ∀ m → Val.Domain.Cover (Tw U m) (Raw.LegalT n m)
    (floors m) (feedback initial floors m)
  floors-covered = covers initial floors
```

`full-grow` 不要求两个组件下标相等或可比，`admitted` 中的坐标与新界
有字面的后继关系。这个正面构造说明“所有世界只能冻结”不是已有否定
的结论；它尚未保证旧折叠的路径律、保留分支或沿运行产生完整输入族。
