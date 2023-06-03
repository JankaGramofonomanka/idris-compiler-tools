declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s1 = internal constant [5 x i8] c"true\00"
@s2 = internal constant [6 x i8] c"false\00"
@s0 = internal constant [4 x i8] c"apa\00"





define i32 @main() {
    entry:
                                                                                                    ;x = 4
                                                                                                    ;x ~ 4
        %r0 = icmp sle i32 3, 4
        br i1 %r0, label %L3, label %L2
    L3:
        %r1 = icmp ne i32 4, 2
        br i1 %r1, label %L4, label %L2
    L4:
        br i1 1, label %L1, label %L2
    L1:
        call void @printBool(i1 1)
        br label %L0
    L2:
        %r3 = getelementptr [4 x i8], [4 x i8]* @s0, i32 0, i32 0
        call void @printString(i8* %r3)
        br label %L0
    L0:
        %r5 = icmp eq i1 1, 1
        br i1 %r5, label %L5, label %L7
    L7:
        %r6 = call i1 @dontCallMe(i32 1)
        br i1 %r6, label %L5, label %L6
    L5:
        br label %L8
    L6:
        br label %L8
    L8:
        %r7 = phi i1 [1, %L5], [0, %L6]
        call void @printBool(i1 %r7)
        %r9 = sub i32 0, 5
        %r10 = icmp slt i32 4, %r9
        br i1 %r10, label %L11, label %L10
    L11:
        %r11 = call i1 @dontCallMe(i32 2)
        br i1 %r11, label %L9, label %L10
    L9:
        br label %L12
    L10:
        br label %L12
    L12:
        %r12 = phi i1 [1, %L9], [0, %L10]
        call void @printBool(i1 %r12)
        %r14 = icmp eq i32 4, 4
        br i1 %r14, label %L15, label %L14
    L15:
        br i1 0, label %L18, label %L17
    L17:
        br label %L19
    L18:
        br label %L19
    L19:
        %r15 = phi i1 [1, %L17], [0, %L18]
        %r16 = icmp eq i1 1, %r15
        br i1 %r16, label %L16, label %L14
    L16:
        br i1 1, label %L13, label %L14
    L13:
        br label %L20
    L14:
        br label %L20
    L20:
        %r17 = phi i1 [1, %L13], [0, %L14]
        call void @printBool(i1 %r17)
        %r19 = call i1 @implies(i1 0, i1 0)
        call void @printBool(i1 %r19)
        %r21 = call i1 @implies(i1 0, i1 1)
        call void @printBool(i1 %r21)
        %r23 = call i1 @implies(i1 1, i1 0)
        call void @printBool(i1 %r23)
        %r25 = call i1 @implies(i1 1, i1 1)
        call void @printBool(i1 %r25)
        ret i32 0
}

define i1 @dontCallMe(i32 %r27) {
    entry:
        call void @printInt(i32 %r27)
        ret i1 1
}

define void @printBool(i1 %r29) {
    entry:
        br i1 %r29, label %L22, label %L23
    L22:
        %r30 = getelementptr [5 x i8], [5 x i8]* @s1, i32 0, i32 0
        call void @printString(i8* %r30)
        br label %L21
    L23:
        %r32 = getelementptr [6 x i8], [6 x i8]* @s2, i32 0, i32 0
        call void @printString(i8* %r32)
        br label %L21
    L21:
        ret void
}

define i1 @implies(i1 %r34, i1 %r35) {
    entry:
        br i1 %r34, label %L26, label %L24
    L26:
        %r36 = icmp eq i1 %r34, %r35
        br i1 %r36, label %L24, label %L25
    L24:
        br label %L27
    L25:
        br label %L27
    L27:
        %r37 = phi i1 [1, %L24], [0, %L25]
        ret i1 %r37
}
