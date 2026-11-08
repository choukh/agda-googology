# 方格首个完整底：参数消去与原回灌公式

这是值分析的校准，不是新的闭项。深度零的完整下降只使用 `Sb 0`
的唯一世界，因此种子和回灌轮数不会改变这一整项；不能把更多轮数
直接解读成首站变强。以下等式覆盖完整树，不是有限展开测试。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GridBaseFirst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (gtX; fl)
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.OutputDrivenFamily as Family
import OCF.Lean.OutputDrivenDown as Down
import OCF.Lean.OutputDrivenGrid as Grid

module W = Family.Family zero hz tt
module D = Down.With W.worlds W.legal
module X = D.St.X zero
module F = Fold S⊥ tt tt

first : Cd
first = D.TN zero

first-grid : ∀ c lc rounds → Grid.At.cell c lc zero rounds ≡ first
first-grid c lc rounds = refl

-- 保留原GT证书：下面H不是只取树值后重造的无证链。
H : F.GT hz → F.GT hz
H b = X.ΦX hz (hs (X.sh₀ (hs hz) (proj₁ b)))
  (proj₂ (X.aS (proj₁ b) tt))
  (⊲ᴮ-tr (hsuc hself) (X.↑S (proj₁ b))) b
  (gtX S⊥ hz (X.sh₀ (hs hz) (proj₁ b)))
  (proj₂ (D.own-path zero (hs hz) hself)
    (X.sh₀ (hs hz) (proj₁ b)) (X.aS (proj₁ b) tt))

whole-root : first ≡ proj₁ (F.limG (F.chainG (hz , tt) H))
whole-root = refl
```

`H` 的回调层号仍是 `1 ⊞ Rich.legS 0 c`，进入其后继公共界；
分支仍是原完整 `gtX`，未替换成单个地板。原链累加，不能当成作者
BTBO 的无累加 typed 迭代。接 `BTBOFull.BTBO≈` 还需完整链的值桥。
