declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;x = 0
                                                                                                    ;x ~ 0
                                                                                                    ;y = 56
                                                                                                    ;y ~ 56
        %r0 = add i32 56, 45
        %r1 = icmp sle i32 %r0, 2
        br i1 %r1, label %L1, label %L2
    L1:
                                                                                                    ;x = 1
                                                                                                    ;x ~ 1
        br label %L0
    L2:
                                                                                                    ;x = 2
                                                                                                    ;x ~ 2
        br label %L0
    L0:
        %r2 = phi i32 [1, %L1], [2, %L2]                                                            ;x
        call void @printInt(i32 %r2)
        ret i32 0
}
