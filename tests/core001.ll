declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s2 = internal constant [9 x i8] c"hello */\00"
@s1 = internal constant [2 x i8] c"=\00"
@s3 = internal constant [9 x i8] c"/* world\00"
@s0 = internal constant [1 x i8] c"\00"





define i32 @main() {
    entry:
        %r0 = call i32 @fac(i32 10)
        call void @printInt(i32 %r0)
        %r2 = call i32 @rfac(i32 10)
        call void @printInt(i32 %r2)
        %r4 = call i32 @mfac(i32 10)
        call void @printInt(i32 %r4)
        %r6 = call i32 @i_fac(i32 10)
        call void @printInt(i32 %r6)
        %r8 = getelementptr [1 x i8], [1 x i8]* @s0, i32 0, i32 0
                                                                                                    ;r = ""
                                                                                                    ;r ~ %r8
                                                                                                    ;n = 10
                                                                                                    ;n ~ 10
                                                                                                    ;r1 = 1
                                                                                                    ;r1 ~ 1
        br label %L1
    L1:
        %r9 = phi i32 [10, %entry], [%r14, %L2]                                                     ;n
        %r10 = phi i8* [%r8, %entry], [%r10, %L2]                                                   ;r
        %r11 = phi i32 [1, %entry], [%r13, %L2]                                                     ;r1
        %r12 = icmp sgt i32 %r9, 0
        br i1 %r12, label %L2, label %L0
    L2:
        %r13 = mul i32 %r11, %r9
                                                                                                    ;r1 = (r1) * (n)
                                                                                                    ;r1 ~ %r13
        %r14 = sub i32 %r9, 1
                                                                                                    ;n = (n) - (1)
                                                                                                    ;n ~ %r14
        br label %L1
    L0:
        call void @printInt(i32 %r11)
        %r16 = getelementptr [2 x i8], [2 x i8]* @s1, i32 0, i32 0
        %r17 = call i8* @repStr(i8* %r16, i32 60)
        call void @printString(i8* %r17)
        %r19 = getelementptr [9 x i8], [9 x i8]* @s2, i32 0, i32 0
        call void @printString(i8* %r19)
        %r21 = getelementptr [9 x i8], [9 x i8]* @s3, i32 0, i32 0
        call void @printString(i8* %r21)
        ret i32 0
}

define i32 @fac(i32 %r23) {
    entry:
                                                                                                    ;r = 0
                                                                                                    ;r ~ 0
                                                                                                    ;n = 0
                                                                                                    ;n ~ 0
                                                                                                    ;r = 1
                                                                                                    ;r ~ 1
                                                                                                    ;n = a
                                                                                                    ;n ~ %r23
        br label %L4
    L4:
        %r24 = phi i32 [%r23, %entry], [%r24, %L5]                                                  ;a
        %r25 = phi i32 [%r23, %entry], [%r29, %L5]                                                  ;n
        %r26 = phi i32 [1, %entry], [%r28, %L5]                                                     ;r
        %r27 = icmp sgt i32 %r25, 0
        br i1 %r27, label %L5, label %L3
    L5:
        %r28 = mul i32 %r26, %r25
                                                                                                    ;r = (r) * (n)
                                                                                                    ;r ~ %r28
        %r29 = sub i32 %r25, 1
                                                                                                    ;n = (n) - (1)
                                                                                                    ;n ~ %r29
        br label %L4
    L3:
        ret i32 %r26
}

define i32 @rfac(i32 %r30) {
    entry:
        %r31 = icmp eq i32 %r30, 0
        br i1 %r31, label %L6, label %L7
    L6:
        ret i32 1
    L7:
        %r32 = sub i32 %r30, 1
        %r33 = call i32 @rfac(i32 %r32)
        %r34 = mul i32 %r30, %r33
        ret i32 %r34
}

define i32 @mfac(i32 %r35) {
    entry:
        %r36 = icmp eq i32 %r35, 0
        br i1 %r36, label %L8, label %L9
    L8:
        ret i32 1
    L9:
        %r37 = sub i32 %r35, 1
        %r38 = call i32 @nfac(i32 %r37)
        %r39 = mul i32 %r35, %r38
        ret i32 %r39
}

define i32 @nfac(i32 %r40) {
    entry:
        %r41 = icmp ne i32 %r40, 0
        br i1 %r41, label %L10, label %L11
    L10:
        %r42 = sub i32 %r40, 1
        %r43 = call i32 @mfac(i32 %r42)
        %r44 = mul i32 %r43, %r40
        ret i32 %r44
    L11:
        ret i32 1
}

define i32 @i_fac(i32 %r45) {
    entry:
        %r46 = call i32 @i_fac2f(i32 1, i32 %r45)
        ret i32 %r46
}

define i32 @i_fac2f(i32 %r47, i32 %r48) {
    entry:
        %r49 = icmp eq i32 %r47, %r48
        br i1 %r49, label %L13, label %L12
    L13:
        ret i32 %r47
    L12:
        %r50 = icmp sgt i32 %r47, %r48
        br i1 %r50, label %L15, label %L14
    L15:
        ret i32 1
    L14:
                                                                                                    ;m = 0
                                                                                                    ;m ~ 0
        %r51 = add i32 %r47, %r48
        %r52 = sdiv i32 %r51, 2
                                                                                                    ;m = ((l) + (h)) / (2)
                                                                                                    ;m ~ %r52
        %r53 = call i32 @i_fac2f(i32 %r47, i32 %r52)
        %r54 = add i32 %r52, 1
        %r55 = call i32 @i_fac2f(i32 %r54, i32 %r48)
        %r56 = mul i32 %r53, %r55
        ret i32 %r56
}

define i8* @repStr(i8* %r57, i32 %r58) {
    entry:
        %r59 = getelementptr [1 x i8], [1 x i8]* @s0, i32 0, i32 0
                                                                                                    ;r = ""
                                                                                                    ;r ~ %r59
                                                                                                    ;i = 0
                                                                                                    ;i ~ 0
        br label %L17
    L17:
        %r60 = phi i32 [0, %entry], [%r66, %L18]                                                    ;i
        %r61 = phi i32 [%r58, %entry], [%r61, %L18]                                                 ;n
        %r62 = phi i8* [%r59, %entry], [%r65, %L18]                                                 ;r
        %r63 = phi i8* [%r57, %entry], [%r63, %L18]                                                 ;s
        %r64 = icmp slt i32 %r60, %r61
        br i1 %r64, label %L18, label %L16
    L18:
        %r65 = call i8* @.strconcat(i8* %r62, i8* %r63)
                                                                                                    ;r = (r) ++ (s)
                                                                                                    ;r ~ %r65
        %r66 = add i32 %r60, 1
                                                                                                    ;i = (i) + (1)
                                                                                                    ;i ~ %r66
        br label %L17
    L16:
        ret i8* %r62
}
