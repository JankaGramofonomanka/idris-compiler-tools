declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s3 = internal constant [5 x i8] c"true\00"
@s0 = internal constant [7 x i8] c"string\00"
@s4 = internal constant [6 x i8] c"false\00"
@s2 = internal constant [14 x i8] c"concatenation\00"
@s1 = internal constant [2 x i8] c" \00"





define i32 @main() {
    entry:
                                                                                                    ;x = 56
                                                                                                    ;x ~ 56
        %r0 = sub i32 0, 23
                                                                                                    ;y = -(23)
                                                                                                    ;y ~ %r0
        %r1 = add i32 56, %r0
        call void @printInt(i32 %r1)
        %r3 = sub i32 56, %r0
        call void @printInt(i32 %r3)
        %r5 = mul i32 56, %r0
        call void @printInt(i32 %r5)
        %r7 = sdiv i32 45, 2
        call void @printInt(i32 %r7)
        %r9 = srem i32 78, 3
        call void @printInt(i32 %r9)
        %r11 = sub i32 56, %r0
        %r12 = add i32 56, %r0
        %r13 = icmp sgt i32 %r11, %r12
        call void @printBool(i1 %r13)
        %r15 = sdiv i32 56, %r0
        %r16 = mul i32 56, %r0
        %r17 = icmp sle i32 %r15, %r16
        call void @printBool(i1 %r17)
        %r19 = getelementptr [7 x i8], [7 x i8]* @s0, i32 0, i32 0
        %r20 = getelementptr [2 x i8], [2 x i8]* @s1, i32 0, i32 0
        %r21 = getelementptr [14 x i8], [14 x i8]* @s2, i32 0, i32 0
        %r22 = call i8* @.strconcat(i8* %r20, i8* %r21)
        %r23 = call i8* @.strconcat(i8* %r19, i8* %r22)
        call void @printString(i8* %r23)
        ret i32 0
}

define void @printBool(i1 %r25) {
    entry:
        br i1 %r25, label %L0, label %L1
    L0:
        %r26 = getelementptr [5 x i8], [5 x i8]* @s3, i32 0, i32 0
        call void @printString(i8* %r26)
        ret void
    L1:
        %r28 = getelementptr [6 x i8], [6 x i8]* @s4, i32 0, i32 0
        call void @printString(i8* %r28)
        ret void
}
