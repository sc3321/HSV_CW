res = set()



for a in range(0,16):
    for b in range(1, a):
        q, r = divmod(a, b)
        res.add((q,r)) 

res_2 = set()

for a in range(0,16):
    for b in range(1, a):
        if (a, b) not in res:
            res_2.add((a,b))

print(res_2)
        