declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s0 = internal constant [4 x i8] c"foo\00"





define i32 @main() {
    entry:
                                                                                                    ;i = 78
                                                                                                    ;i ~ 78
                                                                                                    ;i1 = 1
                                                                                                    ;i1 ~ 1
        call void @printInt(i32 1)
        call void @printInt(i32 78)
        br label %L1
    L1:
        %r2 = phi i32 [78, %entry], [%r5, %L2]                                                      ;i
        %r3 = phi i32 [1, %entry], [%r3, %L2]                                                       ;i1
        %r4 = icmp sgt i32 %r2, 76
        br i1 %r4, label %L2, label %L0
    L2:
        %r5 = sub i32 %r2, 1
                                                                                                    ;i = (i) - (1)
                                                                                                    ;i ~ %r5
        call void @printInt(i32 %r5)
        %r7 = add i32 %r5, 7
                                                                                                    ;i2 = (i) + (7)
                                                                                                    ;i2 ~ %r7
        call void @printInt(i32 %r7)
        br label %L1
    L0:
        call void @printInt(i32 %r2)
        %r10 = icmp sgt i32 %r2, 4
        br i1 %r10, label %L4, label %L5
    L4:
                                                                                                    ;i3 = 4
                                                                                                    ;i3 ~ 4
        call void @printInt(i32 4)
        br label %L3
    L5:
        %r12 = getelementptr [4 x i8], [4 x i8]* @s0, i32 0, i32 0
        call void @printString(i8* %r12)
        br label %L3
    L3:
        call void @printInt(i32 %r2)
        ret i32 0
}
