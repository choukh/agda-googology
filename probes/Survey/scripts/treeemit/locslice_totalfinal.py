# -*- coding: utf-8 -*-
"""同计合法闭项、内部第一位置View、FGH的执行定义依赖。

此为语法近似成本，尚无新高值定理；不得将计数当作1513成品认证。
"""
import os
driver = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'locslice_treeemit.py')
with open(driver, encoding='utf-8') as stream:
    code = stream.read()
code = code.replace("A + 'TreeEmitBuildClosed'", "A + 'RadicalValueNativeFinal'")
code = code.replace("['closed', 'closed-legal', 'fgh']", "['closed', 'closed-view', 'fgh']")
code = code.replace("def sliced(roots):", "new_roots += [('OCF.Free.TotalOrbitRun', 'run')]\n\ndef sliced(roots):")
exec(compile(code, driver, 'exec'), {'__file__': driver, '__name__': '__main__'})
