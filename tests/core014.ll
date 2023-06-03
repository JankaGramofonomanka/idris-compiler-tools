declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;lo = 0
                                                                                                    ;lo ~ 0
                                                                                                    ;hi = 0
                                                                                                    ;hi ~ 0
                                                                                                    ;mx = 0
                                                                                                    ;mx ~ 0
                                                                                                    ;lo = 1
                                                                                                    ;lo ~ 1
                                                                                                    ;hi = lo
                                                                                                    ;hi ~ 1
                                                                                                    ;mx = 5000000
                                                                                                    ;mx ~ 5000000
        call void @printInt(i32 1)
        br label %L1
    L1:
        %r1 = phi i32 [1, %entry], [%r6, %L2]                                                       ;hi
        %r2 = phi i32 [1, %entry], [%r7, %L2]                                                       ;lo
        %r3 = phi i32 [5000000, %entry], [%r3, %L2]                                                 ;mx
        %r4 = icmp slt i32 %r1, %r3
        br i1 %r4, label %L2, label %L0
    L2:
        call void @printInt(i32 %r1)
        %r6 = add i32 %r2, %r1
                                                                                                    ;hi = (lo) + (hi)
                                                                                                    ;hi ~ %r6
        %r7 = sub i32 %r6, %r2
                                                                                                    ;lo = (hi) - (lo)
                                                                                                    ;lo ~ %r7
        br label %L1
    L0:
        ret i32 0
}
