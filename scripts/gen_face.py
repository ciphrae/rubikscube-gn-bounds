import sys; sys.path.insert(0,'scripts')
from rot import *
F=[(0,0,1),(0,0,-1),(0,1,0),(0,-1,0),(1,0,0),(-1,0,0)]
print([F.index(act(k,(0,0,1))) for k in range(24)])
