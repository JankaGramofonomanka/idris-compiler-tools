declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s1 = internal constant [3 x i8] c"||\00"
@s4 = internal constant [5 x i8] c"true\00"
@s3 = internal constant [6 x i8] c"false\00"
@s0 = internal constant [3 x i8] c"&&\00"
@s2 = internal constant [2 x i8] c"!\00"





define i32 @main() {
    entry:
        %r0 = getelementptr [3 x i8], [3 x i8]* @s0, i32 0, i32 0
        call void @printString(i8* %r0)
        %r2 = sub i32 0, 1
        %r3 = call i1 @test(i32 %r2)
        br i1 %r3, label %L2, label %L1
    L2:
        %r4 = call i1 @test(i32 0)
        br i1 %r4, label %L0, label %L1
    L0:
        br label %L3
    L1:
        br label %L3
    L3:
        %r5 = phi i1 [1, %L0], [0, %L1]
        call void @printBool(i1 %r5)
        %r7 = sub i32 0, 2
        %r8 = call i1 @test(i32 %r7)
        br i1 %r8, label %L6, label %L5
    L6:
        %r9 = call i1 @test(i32 1)
        br i1 %r9, label %L4, label %L5
    L4:
        br label %L7
    L5:
        br label %L7
    L7:
        %r10 = phi i1 [1, %L4], [0, %L5]
        call void @printBool(i1 %r10)
        %r12 = call i1 @test(i32 3)
        br i1 %r12, label %L10, label %L9
    L10:
        %r13 = sub i32 0, 5
        %r14 = call i1 @test(i32 %r13)
        br i1 %r14, label %L8, label %L9
    L8:
        br label %L11
    L9:
        br label %L11
    L11:
        %r15 = phi i1 [1, %L8], [0, %L9]
        call void @printBool(i1 %r15)
        %r17 = call i1 @test(i32 234234)
        br i1 %r17, label %L14, label %L13
    L14:
        %r18 = call i1 @test(i32 21321)
        br i1 %r18, label %L12, label %L13
    L12:
        br label %L15
    L13:
        br label %L15
    L15:
        %r19 = phi i1 [1, %L12], [0, %L13]
        call void @printBool(i1 %r19)
        %r21 = getelementptr [3 x i8], [3 x i8]* @s1, i32 0, i32 0
        call void @printString(i8* %r21)
        %r23 = sub i32 0, 1
        %r24 = call i1 @test(i32 %r23)
        br i1 %r24, label %L16, label %L18
    L18:
        %r25 = call i1 @test(i32 0)
        br i1 %r25, label %L16, label %L17
    L16:
        br label %L19
    L17:
        br label %L19
    L19:
        %r26 = phi i1 [1, %L16], [0, %L17]
        call void @printBool(i1 %r26)
        %r28 = sub i32 0, 2
        %r29 = call i1 @test(i32 %r28)
        br i1 %r29, label %L20, label %L22
    L22:
        %r30 = call i1 @test(i32 1)
        br i1 %r30, label %L20, label %L21
    L20:
        br label %L23
    L21:
        br label %L23
    L23:
        %r31 = phi i1 [1, %L20], [0, %L21]
        call void @printBool(i1 %r31)
        %r33 = call i1 @test(i32 3)
        br i1 %r33, label %L24, label %L26
    L26:
        %r34 = sub i32 0, 5
        %r35 = call i1 @test(i32 %r34)
        br i1 %r35, label %L24, label %L25
    L24:
        br label %L27
    L25:
        br label %L27
    L27:
        %r36 = phi i1 [1, %L24], [0, %L25]
        call void @printBool(i1 %r36)
        %r38 = call i1 @test(i32 234234)
        br i1 %r38, label %L28, label %L30
    L30:
        %r39 = call i1 @test(i32 21321)
        br i1 %r39, label %L28, label %L29
    L28:
        br label %L31
    L29:
        br label %L31
    L31:
        %r40 = phi i1 [1, %L28], [0, %L29]
        call void @printBool(i1 %r40)
        %r42 = getelementptr [2 x i8], [2 x i8]* @s2, i32 0, i32 0
        call void @printString(i8* %r42)
        call void @printBool(i1 1)
        call void @printBool(i1 0)
        ret i32 0
}

define void @printBool(i1 %r46) {
    entry:
        br i1 %r46, label %L34, label %L33
    L33:
        %r47 = getelementptr [6 x i8], [6 x i8]* @s3, i32 0, i32 0
        call void @printString(i8* %r47)
        br label %L32
    L34:
        %r49 = getelementptr [5 x i8], [5 x i8]* @s4, i32 0, i32 0
        call void @printString(i8* %r49)
        br label %L32
    L32:
        ret void
}

define i1 @test(i32 %r51) {
    entry:
        call void @printInt(i32 %r51)
        %r53 = icmp sgt i32 %r51, 0
        ret i1 %r53
}
