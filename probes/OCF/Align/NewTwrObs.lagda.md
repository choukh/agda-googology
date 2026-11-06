# 新塔 (五): 最终坍缩里谁有回灌 (第一个障碍的编译陈述)

> 不含记号. 入口 [NewTwr](NewTwr.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 最终坍缩 `collΛ` 是 [GenFoldRun](GenFoldRun.lagda.md) 在 `step KΛc` 上的实例. 折叠里能改变世界的只有两处回灌 (`GenFoldRun` 文件头的表): **新种类的回灌** (第 0, 1 层目标, 新界取 `rd₁` 的读回) 与 **旧种类的 A-回灌** (`fbA κ = inj₁ F`, 新世界取 `rsA F`). 本篇两条定理:
>
> - **`keepΛ`**: `GΛ` 里一切 A-回灌的 `rsA` 都不动任何一站的读回分量 `inj₂ c` (对一切世界, 一切值). 与 `NewTwrK.lossy-rd` (读回分量里的种类没有 A-回灌) 合读: 层号对角的 $\Omega$-结点所在的种类, 它们在世界里的界, 不被任何 A-回灌改变.
> - **`onlyA-rd₁`**: 对一切种类结构 $T$, `GenFoldRd.rd₁` 的读回里的 $\Omega$-结点**都是底种类 `aK` 的** (起点满足时). 所以新种类的回灌喂进去的坐标只含底种类的 $\Omega$-结点. 在 `KΛc` 上底种类是 `(0 , tt)`, 坐标是 `A`.
>
> **只说什么.** 两条都是对定义的形状定理, 不说折叠的值. 由它们得到的 "最终坍缩只在底种类与 `step KΛc` 的新种类上取到新坐标, 层号对角的读回种类只在起始世界的坐标上取分支" 是对折叠全程的判断 (要对 `Run` 的一切中间世界写不变式, 本篇没有写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NewTwrObs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtIf using (Kc; KΛc; nxt; FN)
open import OCF.Align.GenFoldIf
open import OCF.Align.GenFoldTree using (module Tree)
open import OCF.Align.GenFoldInst using (genKc; liftℕ; liftSℕ; liftL; liftSL; upd; upd-Q)
open import OCF.Align.NewTwrColl using (GΛ)
```

## §1 A-回灌不动读回分量

```agda
-- 第 m 站世界的读回分量不变
Kp : ∀ m → Wd (Kc m) → Wd (Kc m) → Set
Kp zero u₀ u = ⊤
Kp (suc s) u₀ u = ∀ c → u (inj₂ c) ≡ u₀ (inj₂ c)

kp-rf : ∀ m u → Kp m u u
kp-rf zero u = tt
kp-rf (suc s) u c = refl

keepSL : ∀ {Q : KS} {κ} (s : FBA Q κ ⊎ ⊤) (F : FBA (nxt Q) (inj₁ tt , κ)) → liftSL s ≡ inj₁ F →
         ∀ w v c → rsA F w v (inj₂ c) ≡ w (inj₂ c)
keepSL (inj₁ F′) .(liftL F′) refl w v c = refl
keepSL (inj₂ _) F ()

keepKc : ∀ n (κ : K (Kc (suc n))) (F : FBA (Kc (suc n)) κ) → fbA (genKc (suc n)) κ ≡ inj₁ F →
         ∀ w v c → rsA F w v (inj₂ c) ≡ w (inj₂ c)
keepKc n (inj₁ tt , κ) F e = keepSL (fbA (genKc n) κ) F e
keepKc n (inj₂ c′ , κ) F ()

keepAt : ∀ n {κ} (F′ : FBA (Kc n) κ) → fbA (genKc n) κ ≡ inj₁ F′ → ∀ u v → Kp n u (rsA F′ u v)
keepAt zero F′ e u v = tt
keepAt (suc n) {κ} F′ e u v c = keepKc n κ F′ e u v c

keepSℕ : ∀ n {κ} (s : FBA (Kc n) κ ⊎ ⊤) → s ≡ fbA (genKc n) κ → (F : FBA KΛc (n , κ)) →
         liftSℕ Kc n s ≡ inj₁ F → ∀ w v m → Kp m (w m) (rsA F w v m)
keepSℕ n (inj₁ F′) e .(liftℕ Kc n F′) refl w v m =
  upd-Q {λ k → Wd (Kc k)} (λ k u → Kp k (w k) u) w n (rsA F′ (w n) v) (λ k → kp-rf k (w k)) (keepAt n F′ (sym e) (w n) v) m
keepSℕ n (inj₂ _) e F ()

keepΛ : ∀ (κ : K KΛc) (F : FBA KΛc κ) → fbA GΛ κ ≡ inj₁ F → ∀ w v s c → rsA F w v (suc s) (inj₂ c) ≡ w (suc s) (inj₂ c)
keepΛ (n , κ) F e w v s = keepSℕ n (fbA (genKc n) κ) refl F e w v (suc s)
```

## §2 新种类的回灌只喂底种类的结点

```agda
data OnlyA {T : KS} (a : K T) : HB T → Set where
  oz : OnlyA a hz
  os : ∀ {x} → OnlyA a x → OnlyA a (hs x)
  ol : ∀ {f} → (∀ n → OnlyA a (f n)) → OnlyA a (hl f)
  oΩ : ∀ {g} → (∀ e → OnlyA a (g e)) → OnlyA a (hΩ a g)

module RdOnly (T : KS) (G : GenK T) (Ld : LgDn T) where
  open Tree T
  open import OCF.Align.GenFoldRd T G Ld using (rd₁; rdp₁; lgW≤; module NbA)
  open NbA

  OA : HB T → Set
  OA = OnlyA {T} (aK G)

  onlyA-nbA : ∀ {b : HB T} {s : A → HB T → HB T} → OA b → (∀ c h → OA h → OA (s c h)) → ∀ c → OA (nbA b s c)
  onlyA-nbA ob os′ azero = ob
  onlyA-nbA ob os′ (asuc c) = os′ c _ (onlyA-nbA ob os′ c)
  onlyA-nbA ob os′ (alim f) = ol (λ n → onlyA-nbA ob os′ (f n))

  onlyA-rd₁  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → OA b → OA (rd₁ lW b x)
  onlyA-rdp₁ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → OA b → ∀ n → OA (rdp₁ lW b d n)
  onlyA-rd₁ lW b n0 ob = ob
  onlyA-rd₁ lW b n1 ob = os ob
  onlyA-rd₁ lW b (x ⨾ y) ob = onlyA-rd₁ lW (rd₁ lW b x) y (onlyA-rd₁ lW b x ob)
  onlyA-rd₁ lW b (nl d) ob = ol (onlyA-rdp₁ lW b d ob)
  onlyA-rd₁ lW b (ni (ss hself) u) ob =
    oΩ (λ e → onlyA-nbA ob (λ c h oh → onlyA-rd₁ lW h (u ≤rf lW (toD₀ c)) oh) (frE G e))
  onlyA-rd₁ lW b (nc (inj₁ κ) z u) ob = onlyA-rd₁ lW b (u ≤rf lW) ob
  onlyA-rd₁ lW b (nc (inj₂ _) () u) ob
  onlyA-rd₁ lW b (nw p x) ob = onlyA-rd₁ (lgW≤ p lW) b x ob
  onlyA-rdp₁ lW b d ob zero = ob
  onlyA-rdp₁ lW b d ob (suc n) = onlyA-rd₁ lW (rdp₁ lW b d n) (d n) (onlyA-rdp₁ lW b d ob n)
```

**在 `KΛc` 上.** 底种类是第 0 站 (`S₀`) 的唯一种类.

```agda
aKΛ : aK GΛ ≡ (0 , tt)
aKΛ = refl
```
