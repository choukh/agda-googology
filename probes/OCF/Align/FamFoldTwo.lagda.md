# 族增量世界上的真折叠 (二): 第二级 (κ₃)

> 不含记号. 入口 [FamFold](FamFold.lagda.md), 接口 [FamFoldIf](FamFoldIf.lagda.md), 第一级 [FamFoldOne](FamFoldOne.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 第二级的新种类是 `Slot` 在坐标 $2$ 处的槽种类, 坐标 `HB (G₀ (fin 2)) = HB S₂`. 层是 `HB S₃` (`S₃ = step S₂`, 四种种类). 与第一级同法, 只多一件东西: **第 3 层的读回 `rd₃`** (两种种类折叠第 3 层的数据树读成 `HB S₂`), 与 `HtTowerNRead.rd₂` 同形, 多一种节点 (过第 2 层的节点读成 κ₂ 的 $\Omega$-分支, 坐标 $x$ 喂 `toD₂ x`). 合法由形状给出 (`Lg-rd₃`, 只要底合法).
>
> **折叠** `F3.fold`: 层 `HB S₃` ↦ 第 3 层的数据树. 旧种类 `κA`, `κH` 同第一级 (`nκ`, `nμ`); **旧种类 κ₂** (坐标 `HB S₁`) 的 $\Omega$-节点 ↦ 过第 2 层的节点 `ni (ss hself)`, 输入 $y$ (第 2 层的树) 经 `rd₂` 读成坐标; **新种类 κ₃** 的 $\Omega$-节点 ↦ 回灌: 世界链在 $(2,p_0)$ 处族更新 (`rFC`, 连 `hs 2` 的拷贝), 增量是折叠自己在分支上的输出经 `rd₃`, 第一级的下降 `FamFoldOne.idx`, 两种种类折叠 $\Omega_{3\boxplus h}$ 的第 3 层输出, `rd₃` 读回. 读回的族 `cast₂` 只按坐标的构造子定义, `cast₂ 2 x = x` 定义相等.
>
> **闭项** `T₄ Λ = T₃ (idx₃ Λ)`: 第二级把 `HB S₃` 的层折成 `HB S₂`, 第一级再折成两种种类的层, 交给 `T⁺`. 级顶 `Tᵀ₂ = T₄ (Ωtop S₂)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldTwo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop; nbᴮ; nb-contB; cont→Lg)
open import OCF.Align.HtTowerFTree
  using (S₁; H₀; Ht; Wd₂; LgW₂; κA; κH; D; StH; ss; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; lgW≤)
open import OCF.Align.HtTowerFRead using (toD; lwκ; pwκ)
open import OCF.Align.HtTowerNRead using (D₂; toD₁; xμ; lxμ; ≤μ; rd₂; Lg-rd₂)
open import OCF.Align.HtTowerFClosed using (module At; ord; W₁)
open import OCF.Align.DiagK3Zero using (_≈_; ≈l)
open import OCF.Align.DiagK3One using (NoNew; up-noNew)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (fin; lg-fin)
open import OCF.Align.LocUipIf using (Inc; atF; monoF; legalF; cohF; CopyCoh)
open import OCF.Align.LocUipFeed using (rFC; raiseFCᴮ; copyFC)
open import OCF.Align.UipFbClosed using (vz; lgvz; cohvz; noNew-≈)
open import OCF.Align.FamFoldIf using (S₂; κ₂; CohC; slotAt; Fold₁)
open import OCF.Align.FamFoldOne using (idx; Lg-idx; T₃)
open Slot

S₃ : KS
S₃ = step S₂

D₃ : Wd₂ → Set
D₃ = D (hs (hs (hs hz)))
```

## §1 两种旧种类上的连续分支 (输出在 `HB S₂`)

```agda
-- κA: 对 A 坐标递归
nbA₂ : HB S₂ → (A → HB S₂ → HB S₂) → A → HB S₂
nbA₂ b s azero = b
nbA₂ b s (asuc c) = s c (nbA₂ b s c)
nbA₂ b s (alim f) = hl (λ n → nbA₂ b s (f n))

-- κH: 对 H₀ 坐标递归, H₀ 的 Ω-极限 (A 坐标) 读成 κA
nbH₂ : HB S₂ → (H₀ → HB S₂ → HB S₂) → H₀ → HB S₂
nbH₂ b s hz = b
nbH₂ b s (hs x) = s x (nbH₂ b s x)
nbH₂ b s (hl f) = hl (λ n → nbH₂ b s (f n))
nbH₂ b s (hΩ tt h) = hΩ (inj₁ κA) (λ c → nbH₂ b s (h c))

module _ {b : HB S₂} {s : A → HB S₂ → HB S₂} (fs : ∀ c h {w} → h ⊲[ w ] s c h) where
  nbA₂-mono : ∀ {c c′} → c ⊲ c′ → ∀ {w} → nbA₂ b s c ⊲[ w ] nbA₂ b s c′
  nbA₂-mono C.self = hself
  nbA₂-mono (C.suc p) = ⊲ᴮ-tr (nbA₂-mono p) (fs _ _)
  nbA₂-mono (C.lim n p) = hlim n (nbA₂-mono p)

  Lg-nbA₂ : LgB b → (∀ c h → LgB h → LgB (s c h)) → LgB {S₂} (hΩ (inj₁ κA) (nbA₂ b s))
  Lg-nbA₂ lb ls = (λ lw e e′ p → nbA₂-mono p) , lg
    where
    lg : ∀ c → Lg c → LgB (nbA₂ b s c)
    lg azero _ = lb
    lg (asuc c) l = ls c _ (lg c l)
    lg (alim f) (st , l) = (λ n → nbA₂-mono (st n)) , (λ n → lg (f n) (l n))

module _ {b : HB S₂} {s : H₀ → HB S₂ → HB S₂} (fs : ∀ x h {w} → h ⊲[ w ] s x h) where
  nbH₂-mono : ∀ {x y : H₀} {a β γ} → x ⊲[ a ] y → nbH₂ b s x ⊲[ ((a , β) , γ) ] nbH₂ b s y
  nbH₂-mono hself = hself
  nbH₂-mono (hsuc p) = ⊲ᴮ-tr (nbH₂-mono p) (fs _ _)
  nbH₂-mono (hlim n p) = hlim n (nbH₂-mono p)
  nbH₂-mono (hLim e p) = hLim {κ = inj₁ κA} e (nbH₂-mono p)

  Lg-nbH₂ : LgB b → (∀ x h → LgB h → LgB (s x h)) → LgB {S₂} (hΩ (inj₁ κH) (nbH₂ b s))
  Lg-nbH₂ lb ls = (λ lw e e′ p → nbH₂-mono p) , lg
    where
    lg : ∀ x → LgB x → LgB (nbH₂ b s x)
    lg hz _ = lb
    lg (hs x) l = ls x _ (lg x l)
    lg (hl f) (st , l) = (λ {w} n → nbH₂-mono {a = proj₁ (proj₁ w)} {proj₂ (proj₁ w)} {proj₂ w} (st n)) , (λ n → lg (f n) (l n))
    lg (hΩ tt h) (mo , l) =
      (λ {w} lw e e′ p → nbH₂-mono {a = proj₁ (proj₁ w)} {proj₂ (proj₁ w)} {proj₂ w} (mo (proj₁ (proj₁ lw)) e e′ p)) ,
      (λ c lc → lg (h c) (l c lc))
```

## §2 第 3 层读回成 `HB S₂`

```agda
-- HB S₁ 的高度读成第 2 层的树 (旧种类的 Ω-极限读成闭包)
toD₂ : ∀ {W} → Ht → D₂ W
toD₂ hz = n0
toD₂ (hs x) = toD₂ x ⨾ n1
toD₂ (hl f) = nl (λ n → toD₂ (f n))
toD₂ (hΩ (inj₁ tt) h) = nκ tt (λ {c} _ _ → toD₂ (h c))
toD₂ (hΩ (inj₂ tt) h) = nμ tt (λ {W′} _ _ → toD₂ (h (proj₂ W′)))

rd₃  : ∀ {W} → LgW₂ W → HB S₂ → D₃ W → HB S₂
rdp₃ : ∀ {W} → LgW₂ W → HB S₂ → (ℕ → D₃ W) → ℕ → HB S₂
rd₃ lW b n0 = b
rd₃ lW b n1 = hs b
rd₃ lW b (x ⨾ y) = rd₃ lW (rd₃ lW b x) y
rd₃ lW b (nl d) = hl (rdp₃ lW b d)
rd₃ lW b (ni (ss hself) u) = hΩ κ₂ (nbᴮ b (λ x h → rd₃ lW h (u ≤rf lW (toD₂ x))))
rd₃ lW b (ni (ss (hsuc hself)) u) = hΩ (inj₁ κH) (nbH₂ b (λ x h → rd₃ lW h (u ≤rf lW (toD₁ x))))
rd₃ lW b (ni (ss (hsuc (hsuc hself))) u) = hΩ (inj₁ κA) (nbA₂ b (λ c h → rd₃ lW h (u ≤rf lW (toD c))))
rd₃ {W} lW b (nκ _ u) =
  hΩ (inj₁ κA) (nbA₂ b (λ c h → rd₃ (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))))
rd₃ {W} lW b (nμ _ u) =
  hΩ (inj₁ κH) (nbH₂ b (λ x h → rd₃ (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x))))
rd₃ lW b (nw p x) = rd₃ (lgW≤ p lW) b x
rdp₃ lW b d zero = b
rdp₃ lW b d (suc n) = rd₃ lW (rdp₃ lW b d n) (d n)

rd₃-fst : ∀ {W} (lW : LgW₂ W) b (x : D₃ W) {w} → b ⊲[ w ] rd₃ lW b x
rd₃-fst lW b n0 = hself
rd₃-fst lW b n1 = hsuc hself
rd₃-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rd₃-fst lW b x) (rd₃-fst lW (rd₃ lW b x) y)
rd₃-fst lW b (nl d) = hlim 0 hself
rd₃-fst lW b (ni (ss hself) u) {w} = hLim {S₂} {κ = κ₂} {c = hz} (z⊲ᴮ (proj₂ w)) hself
rd₃-fst lW b (ni (ss (hsuc hself)) u) {w} = hLim {S₂} {κ = inj₁ κH} {c = hz} (z⊲ᴮ (proj₂ (proj₁ w))) hself
rd₃-fst lW b (ni (ss (hsuc (hsuc hself))) u) {w} = hLim {S₂} {κ = inj₁ κA} {c = azero} (z⊲ (proj₁ (proj₁ w))) hself
rd₃-fst lW b (nκ _ u) {w} = hLim {S₂} {κ = inj₁ κA} {c = azero} (z⊲ (proj₁ (proj₁ w))) hself
rd₃-fst lW b (nμ _ u) {w} = hLim {S₂} {κ = inj₁ κH} {c = hz} (z⊲ᴮ (proj₂ (proj₁ w))) hself
rd₃-fst lW b (nw p x) = rd₃-fst (lgW≤ p lW) b x

Lg-rd₃  : ∀ {W} (lW : LgW₂ W) b (x : D₃ W) → LgB b → LgB (rd₃ lW b x)
Lg-rdp₃ : ∀ {W} (lW : LgW₂ W) b (d : ℕ → D₃ W) → LgB b → ∀ n → LgB (rdp₃ lW b d n)
Lg-rd₃ lW b n0 l = l
Lg-rd₃ lW b n1 l = l
Lg-rd₃ lW b (x ⨾ y) l = Lg-rd₃ lW (rd₃ lW b x) y (Lg-rd₃ lW b x l)
Lg-rd₃ lW b (nl d) l = (λ n → rd₃-fst lW (rdp₃ lW b d n) (d n)) , Lg-rdp₃ lW b d l
Lg-rd₃ lW b (ni (ss hself) u) l =
  cont→Lg (nb-contB l (λ x h → rd₃-fst lW h (u ≤rf lW (toD₂ x))) (λ x h lh → Lg-rd₃ lW h (u ≤rf lW (toD₂ x)) lh))
Lg-rd₃ lW b (ni (ss (hsuc hself)) u) l =
  Lg-nbH₂ (λ x h → rd₃-fst lW h (u ≤rf lW (toD₁ x))) l (λ x h lh → Lg-rd₃ lW h (u ≤rf lW (toD₁ x)) lh)
Lg-rd₃ lW b (ni (ss (hsuc (hsuc hself))) u) l =
  Lg-nbA₂ (λ c h → rd₃-fst lW h (u ≤rf lW (toD c))) l (λ c h lh → Lg-rd₃ lW h (u ≤rf lW (toD c)) lh)
Lg-rd₃ {W} lW b (nκ _ u) l =
  Lg-nbA₂ (λ c h → rd₃-fst (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW)))) l
          (λ c h lh → Lg-rd₃ (lwκ c (proj₁ lW) , proj₂ lW) h (u (pwκ (proj₁ W) c) (lwκ c (proj₁ lW))) lh)
Lg-rd₃ {W} lW b (nμ _ u) l =
  Lg-nbH₂ (λ x h → rd₃-fst (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x))) l
          (λ x h lh → Lg-rd₃ (proj₁ lW , lxμ lW x) h (u (≤μ lW x) (proj₁ lW , lxμ lW x)) lh)
Lg-rd₃ lW b (nw p x) l = Lg-rd₃ (lgW≤ p lW) b x l
Lg-rdp₃ lW b d l zero = l
Lg-rdp₃ lW b d l (suc n) = Lg-rd₃ lW (rdp₃ lW b d n) (d n) (Lg-rdp₃ lW b d l n)
```

## §3 第 3 层目标上的输出与读回

```agda
top₃ : Ht → Ht
top₃ h = hs (hs (hs hz)) ⊞ h

Lg-top₃ : ∀ h → LgB h → LgB (top₃ h)
Lg-top₃ h lh = Lg-⊞ (hs (hs (hs hz))) h tt lh

o₃ : ∀ h {w} → hs hz ⊲[ w ] top₃ h
o₃ h = ⊲ᴮ-tr (hsuc (hsuc hself)) (⊞-fst (hs (hs (hs hz))) h)

module O₃ (h : Ht) (lh : LgB h) where
  open At (top₃ h) (Lg-top₃ h lh) (o₃ h) public
  τ₃ : Tg W₁ (hs (hs (hs hz))) W₁
  τ₃ = tg ≤rf (⊞-fst (hs (hs (hs hz))) h) (tt , tt)
  out₃ : D₃ W₁
  out₃ = yc ΔΩ τ₃

δ₃⋆ : (h : Ht) → LgB h → HB S₂
δ₃⋆ h lh = rd₃ (tt , tt) (hs hz) (O₃.out₃ h lh)

lδ₃⋆ : ∀ h lh → LgB (δ₃⋆ h lh)
lδ₃⋆ h lh = Lg-rd₃ (tt , tt) (hs hz) (O₃.out₃ h lh) tt

-- 第 3 层输出 (对一切世界)
Out₃ : Set
Out₃ = (W : Wd₂) → D₃ W

lay₃ : Out₃ → HB S₂
lay₃ o = rd₃ (tt , tt) hz (o W₁)

Lg-lay₃ : ∀ o → LgB (lay₃ o)
Lg-lay₃ o = Lg-rd₃ (tt , tt) hz (o W₁) tt

-- 读回: 输出读成 HB S₂, 经第一级下降成两种种类的层, 两种种类折叠 Ω_{3 ⊞ ·} 的第 3 层输出读回 HB S₂
rdO₃ : Out₃ → HB S₂
rdO₃ o = δ₃⋆ (idx (lay₃ o)) (Lg-idx (lay₃ o))

lg-rdO₃ : ∀ o → LgB (rdO₃ o)
lg-rdO₃ o = lδ₃⋆ (idx (lay₃ o)) (Lg-idx (lay₃ o))

c₂ : HB S₀
c₂ = fin 2

cast₂ : (c : HB S₀) → HB S₂ → HB (G₀ c)
cast₂ (hs (hs hz)) x = x
cast₂ (hs (hs (hs c))) x = up (cast₂ (hs (hs c)) x)
cast₂ (hs (hs (hl f))) x = hz
cast₂ (hs (hs (hΩ κ g))) x = hz
cast₂ hz x = hz
cast₂ (hs hz) x = hz
cast₂ (hs (hl f)) x = hz
cast₂ (hs (hΩ κ g)) x = hz
cast₂ (hl f) x = hz
cast₂ (hΩ κ g) x = hz

famRd₂ : HB S₂ → Inc
famRd₂ x c = cast₂ c x

-- 读回对坐标一致
famO₂ : Σ (Out₃ → Inc) (λ F → ∀ o → F o c₂ ≡ rdO₃ o)
famO₂ = (λ o → famRd₂ (rdO₃ o)) , (λ o → refl)
```

## §4 折叠

```agda
module F3 (w : Out) (lo : LgO w) (p₀ : AdmE w c₂) where
  slot : Cmp w → HB S₂
  slot u = slotAt u c₂ p₀

  ch : (Cmp w → Out₃) → Cmp w → ℕ → Cmp w
  ch Fo v zero = v
  ch Fo v (suc n) = rFC w lo (ch Fo v n) c₂ p₀ (famRd₂ (rdO₃ (Fo (ch Fo v n))))

  fold : Cmp w → HB S₃ → Out₃
  fold v hz W = n0
  fold v (hs x) W = fold v x W ⨾ n1
  fold v (hl f) W = nl (λ n → fold v (f n) W)
  fold v (hΩ (inj₁ (inj₁ (inj₁ tt))) g) W = nκ tt (λ {c} _ _ → fold v (g c) (c , proj₂ W))
  fold v (hΩ (inj₁ (inj₁ (inj₂ tt))) g) W = nμ tt (λ {W′} _ _ → fold v (g (proj₂ W′)) W′)
  fold v (hΩ (inj₁ (inj₂ tt)) g) W = ni (ss hself) (λ {W′} _ lW′ y → fold v (g (rd₂ lW′ hz y)) W′)
  fold v (hΩ (inj₂ tt) g) W =
    nl (λ n → fold (ch (λ u → fold u (g (slot u))) v n) (g (slot (ch (λ u → fold u (g (slot u))) v n))) W)

  chain : Cmp w → (HB S₂ → HB S₃) → ℕ → Cmp w
  chain v g = ch (λ u → fold u (g (slot u))) v

  fold-Ω : ∀ v g W → fold v (hΩ (inj₂ tt) g) W ≡ nl (λ n → fold (chain v g n) (g (slot (chain v g n))) W)
  fold-Ω v g W = refl

  ch-lg : ∀ v g → LgWᴮ (w , v) → ∀ n → LgWᴮ (w , chain v g n)
  ch-lg v g lW zero = lW
  ch-lg v g lW (suc n) =
    legalF raiseFCᴮ w lo (chain v g n) c₂ p₀ _ (lg-rdO₃ (fold (chain v g n) (g (slot (chain v g n))))) (ch-lg v g lW n)

  ch-coh : ∀ v g → CohC (w , v) → ∀ n → CohC (w , chain v g n)
  ch-coh v g cc zero = cc
  ch-coh v g cc (suc n) =
    cohF raiseFCᴮ w lo (chain v g n) c₂ p₀ _ (proj₁ (ch-coh v g cc n)) ,
    copyFC w lo (chain v g n) c₂ p₀ _ (proj₂ (ch-coh v g cc n))

  ch-≤ : ∀ v g n → (w , chain v g n) ≤ᴮ (w , chain v g (suc n))
  ch-≤ v g n = monoF raiseFCᴮ w lo (chain v g n) c₂ p₀ _

  slot-s : ∀ v g n → slot (chain v g (suc n)) ≡ slot (chain v g n) ⊞ rdO₃ (fold (chain v g n) (g (slot (chain v g n))))
  slot-s v g n = cong proj₂ (atF raiseFCᴮ w lo (chain v g n) c₂ p₀ _)

  slot-bd : ∀ v g n → Bdᴮ (c₂ , inj₂ tt) (slot (chain v g n)) (w , chain v g n)
  slot-bd v g n = p₀ , hself
```

## §5 闭项

外层世界 $(0,3)$: 坐标 $2$ 与它的后继 $3$ 都可入 (拷贝在 $3$ 的分量里).

```agda
w₃ : Out
w₃ = azero , fin 3

lo₃ : LgO w₃
lo₃ = tt , lg-fin 3

p₂ : AdmE w₃ c₂
p₂ = hsuc hself

copyvz₃ : CopyCoh (w₃ , vz w₃)
copyvz₃ c₀ q₀ q₁ = refl

cohC₃ : CohC (w₃ , vz w₃)
cohC₃ = cohvz w₃ , copyvz₃

module F₃ = F3 w₃ lo₃ p₂

idx₃ : HB S₃ → HB S₂
idx₃ Λ = lay₃ (F₃.fold (vz w₃) Λ)

Lg-idx₃ : ∀ Λ → LgB (idx₃ Λ)
Lg-idx₃ Λ = Lg-lay₃ (F₃.fold (vz w₃) Λ)

T₄ : (Λ : HB S₃) → LgB Λ → A
T₄ Λ _ = T₃ (idx₃ Λ) (Lg-idx₃ Λ)

Tᵀ₂ : A
Tᵀ₂ = T₄ (Ωtop S₂) (Lg-Ωtop S₂)

fghᵀ₂ : ℕ → ℕ
fghᵀ₂ = FL.FGH (ord Tᵀ₂)
```

## §6 第二级的级顶不被压回

级顶 `Ωtop S₂` 的第二级输入 (`HB S₂`) 是格的 ℕ-极限; 第 2 格的最外是 κ₂ 的 $\Omega$-节点, 所以它含 `S₂` 的新种类节点, 不与任何 `HB S₁` 嵌入 `up h` 互模拟 (对照 `UipFbTop.pr₂-top`: 投影把同一个级顶压回 `Ω₂ᴴ`).

```agda
pieces₃ : ℕ → D₃ W₁
pieces₃ n = F₃.fold (F₃.chain (vz w₃) up n) (up (F₃.slot (F₃.chain (vz w₃) up n))) W₁

cells₃ : ℕ → HB S₂
cells₃ = rdp₃ (tt , tt) hz pieces₃

top₃-hl : idx₃ (Ωtop S₂) ≡ hl cells₃
top₃-hl = refl

isκ₂ : HB S₂ → Set
isκ₂ (hΩ (inj₂ tt) _) = ⊤
isκ₂ _ = ⊥

cell₃-κ₂ : isκ₂ (cells₃ 2)
cell₃-κ₂ = tt

cell₃-new : ¬ NoNew (cells₃ 2)
cell₃-new ()

¬top₂≈up : ∀ (h : Ht) → ¬ (idx₃ (Ωtop S₂) ≈ up h)
¬top₂≈up (hl f) (≈l e) = cell₃-new (noNew-≈ (e 2) (up-noNew (f 2)))

-- 世界侧: 链上第 1 个世界的槽含 κ₂ 节点, 有界; 链上世界合法, 两种相干
slot₃-new : ¬ NoNew (F₃.slot (F₃.chain (vz w₃) up 1))
slot₃-new ()

slot₃-bd : Bdᴮ (c₂ , inj₂ tt) (F₃.slot (F₃.chain (vz w₃) up 1)) (w₃ , F₃.chain (vz w₃) up 1)
slot₃-bd = F₃.slot-bd (vz w₃) up 1

chain₃-lg : ∀ n → LgWᴮ (w₃ , F₃.chain (vz w₃) up n)
chain₃-lg = F₃.ch-lg (vz w₃) up (lgvz w₃ lo₃)

chain₃-coh : ∀ n → CohC (w₃ , F₃.chain (vz w₃) up n)
chain₃-coh = F₃.ch-coh (vz w₃) up cohC₃
```
