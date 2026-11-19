import re,sys,statistics as st,collections
# usage: an.py LOG   (medians over rounds, in microseconds, and ratios to rind)
d=collections.defaultdict(list)
for l in open(sys.argv[1]):
    m=re.match(r'r(\d+) (\w+) (\w+) median_ns (\d+) min_ns (\d+) p90_ns (\d+)',l)
    if m: d[(m[3],m[2])].append(int(m[4]))
ops=['keygen','ecdh','ecdsakeygen','sign','verify']
res={}
print('op lib rounds median_us min_us max_us spread%')
for op in ops:
    for lib in ['rind','rind2','openssl','awslc','ring']:
        v=d.get((op,lib),[])
        if not v: continue
        med=st.median(v); res[(op,lib)]=med
        print(op,lib,len(v),f'{med/1000:.1f}',f'{min(v)/1000:.1f}',f'{max(v)/1000:.1f}',f'{(max(v)-min(v))/med*100:.1f}')
print()
for op in ops:
    for lib in ['rind2','openssl','awslc','ring']:
        if (op,'rind') in res and (op,lib) in res:
            print(op,'rind/'+lib,'%.3f'%(res[(op,'rind')]/res[(op,lib)]))
