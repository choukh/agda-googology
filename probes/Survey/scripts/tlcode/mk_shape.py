import re,sys
src=open('LadderOrdPos.lagda.md',encoding='utf8').read()
# cut pieces
def sect(a,b):
    i=src.index(a); j=src.index(b,i) if b else len(src)
    return src[i:j]
s1=sect('## §1 码与位置','## §3 秩')
s4=sect('## §4 根','## §6 实例')
head='''# 严格列 (一): 块形与位置

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** `Sh` 只记块的形状: `sz` 空段, `ss` 上面加一个点, `sl g` 一列块. **这里没有值**: 没有 `plus`, `val`, `rk`, 也不读 `Ordᴵ`. 值和秩在 [TLCodeLit](TLCodeLit.lagda.md) 由严格列直接读出. 序, 三歧, 根, 第 0 行的写法与形状有关, 与值无关, 所以这部分和 [LadderOrdPos](LadderOrdPos.lagda.md) §1, §2, §4, §5 逐行相同, 只改了名字 (`Code` → `Sh`, `cz` → `sz`, `cs` → `ss`, `cl` → `sl`, `fstC` → `fstS`, `botC` → `botS`); 生成脚本是一次性的 `sed` 式替换, 没有留. 本文件的导入闭包不含 `LadderOrdPos`, `LadderOrdCode`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.LadderOrdBase using (Tri; tlt; teq; tgt; View; base; clos; chain; ViewOk)
```

'''
body=s1+s4
body=body.replace('fstC','fstS').replace('botC','botS')
body=re.sub(r'\bCode\b','Sh',body)
body=re.sub(r'\bcz\b','sz',body)
body=re.sub(r'\bcs\b','ss',body)
body=re.sub(r'\bcl\b','sl',body)
body=body.replace('## §1 码与位置','## §1 块形与位置').replace('## §4 根','## §3 根').replace('## §5 第 0 行的写法','## §4 第 0 行的写法')
body=body.replace('`viewC` 走位置的路径','`viewC` 走位置的路径')
open(sys.argv[1],'w',encoding='utf8').write(head+body)
