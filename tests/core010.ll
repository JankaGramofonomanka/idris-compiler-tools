declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = call i32 @fac(i32 5)
        call void @printInt(i32 %r0)
        ret i32 0
}

define i32 @fac(i32 %r2) {
    entry:
                                                                                                    ;r = 0
                                                                                                    ;r ~ 0
                                                                                                    ;n = 0
                                                                                                    ;n ~ 0
                                                                                                    ;r = 1
                                                                                                    ;r ~ 1
                                                                                                    ;n = a
                                                                                                    ;n ~ %r2
        br label %L1
    L1:
        %r3 = phi i32 [%r2, %entry], [%r3, %L2]                                                     ;a
        %r4 = phi i32 [%r2, %entry], [%r8, %L2]                                                     ;n
        %r5 = phi i32 [1, %entry], [%r7, %L2]                                                       ;r
        %r6 = icmp sgt i32 %r4, 0
        br i1 %r6, label %L2, label %L0
    L2:
        %r7 = mul i32 %r5, %r4
                                                                                                    ;r = (r) * (n)
                                                                                                    ;r ~ %r7
        %r8 = sub i32 %r4, 1
                                                                                                    ;n = (n) - (1)
                                                                                                    ;n ~ %r8
        br label %L1
    L0:
        ret i32 %r5
}
