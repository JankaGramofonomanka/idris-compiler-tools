declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;y = 17
                                                                                                    ;y ~ 17
        br label %L1
    L1:
        %r0 = phi i32 [17, %entry], [%r2, %L2]                                                      ;y
        %r1 = icmp sgt i32 %r0, 0
        br i1 %r1, label %L2, label %L0
    L2:
        %r2 = sub i32 %r0, 2
                                                                                                    ;y = (y) - (2)
                                                                                                    ;y ~ %r2
        br label %L1
    L0:
        %r3 = icmp slt i32 %r0, 0
        br i1 %r3, label %L3, label %L4
    L3:
        call void @printInt(i32 0)
        ret i32 0
    L4:
        call void @printInt(i32 1)
        ret i32 0
}
