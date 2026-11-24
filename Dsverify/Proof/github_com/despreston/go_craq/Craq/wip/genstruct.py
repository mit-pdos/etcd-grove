# generate a struct-encoder proof body
APP1 = ["wp_apply wp_slice_literal (V := w8) _","isplitr","· ipureintro; rfl","iintro %sl1 ⟨Hsl1, -⟩",
        "wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩"]
def field(kind, arg, i, extra=None):
    h=f"h{i}"
    L=[]
    if kind=='str':
        L.append(f"wp_apply wp_rpcSent_t5 {arg}")
        L.append(f"by_cases {h} : {arg} = [] <;> simp only [{h}, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]")
        enc=f"wp_apply wp_rpcEnc_t5 {arg} _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩"
    elif kind=='u64':
        L.append(f"wp_apply wp_rpcSent_t6 {arg}")
        L.append(f"by_cases {h} : {arg} = W64 0 <;> simp only [{h}, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]")
        enc=f"wp_apply wp_rpcEnc_t6 {arg} _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩"
    elif kind=='bool':
        L.append(f"wp_apply wp_rpcSent_t29 {arg}")
        L.append(f"cases {h} : {arg}")
        enc=f"wp_apply wp_rpcEnc_t29 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩"
    elif kind=='bytes':
        sl,dq,x=extra
        L.append(f"wp_apply wp_rpcSent_t11 {sl} {dq} {x} $$ [$Hsl] as Hsl")
        L.append(f"by_cases {h} : {x} = [] <;> simp only [{h}, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]")
        enc=f"wp_apply wp_rpcEnc_t11 {sl} {dq} {x} _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩"
    body=["(try wp_auto)"]+APP1+["(try wp_auto)", f"(try ({enc}))"]
    L.append("all_goals (")
    L += ["  "+b for b in body]
    L.append("  )")
    return ["all_goals ("]+["  "+x for x in ["(try wp_auto)"]+L[:2]]+["  )"]+L[2:]
def proof(fields, ind="  "):
    L=["(try wp_auto)"]+APP1
    for i,f in enumerate(fields):
        L+=field(*f, i=i+1) if len(f)==2 else field(f[0],f[1],i+1,f[2])
    return "\n".join(ind+l for l in L)
if __name__=="__main__":
    print(proof([('str','k'),('u64','v')]))
