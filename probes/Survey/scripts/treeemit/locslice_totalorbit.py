# -*- coding: utf-8 -*-
"""与旧高闭项同口径比较 TotalOrbit 的闭项/合法性/FGH 执行依赖。

先成功生成新 TotalOrbitClosed 的全部 HTML；旧侧 HTML 可以来自原
TreeEmitBuildAccept 成功轮，旧数学文件须未改。标准库两侧均不计。
这只量执行定义，不认证新值、内部 View 或 1513 成品目标。
"""
import os

driver = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'locslice_treeemit.py')
with open(driver, encoding='utf-8') as stream:
    code = stream.read()
code = code.replace("A + 'TreeEmitBuildClosed'", "A + 'TotalOrbitClosed'")
# 记录模块实例的隐参在HTML中不总是链接到实际记录值。显式补足
# open TotalInterpreter interpreter 的实例及其三个字段，避免漏计核心。
code = code.replace("def sliced(roots):", "new_roots += [('OCF.Free.TotalOrbitRun', 'run')] + [('OCF.Free.TotalOrbitBuild', x) for x in ['interpreter', 'read', 'lawful']]\n\ndef sliced(roots):")
# 保留同一切块器、旧根、别名补根及所有其他统计规则。
exec(compile(code, driver, 'exec'), {'__file__': driver, '__name__': '__main__'})
