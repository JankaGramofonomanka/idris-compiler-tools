declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
                                                                                                    ;a = 1
                                                                                                    ;a ~ 1
                                                                                                    ;b = 2
                                                                                                    ;b ~ 2
                                                                                                    ;c = 1
                                                                                                    ;c ~ 1
                                                                                                    ;d = 2
                                                                                                    ;d ~ 2
                                                                                                    ;e = 1
                                                                                                    ;e ~ 1
                                                                                                    ;f = 2
                                                                                                    ;f ~ 2
                                                                                                    ;g = 1
                                                                                                    ;g ~ 1
                                                                                                    ;h = 2
                                                                                                    ;h ~ 2
                                                                                                    ;i = 1
                                                                                                    ;i ~ 1
                                                                                                    ;j = 2
                                                                                                    ;j ~ 2
                                                                                                    ;k = 1
                                                                                                    ;k ~ 1
                                                                                                    ;l = 2
                                                                                                    ;l ~ 2
                                                                                                    ;m = 1
                                                                                                    ;m ~ 1
                                                                                                    ;n = 2
                                                                                                    ;n ~ 2
        %r0 = call i32 @foo(i32 1, i32 2, i32 1, i32 2, i32 1, i32 2, i32 1, i32 2, i32 1, i32 2, i32 1, i32 2, i32 1, i32 2)
        ret i32 %r0
}

define i32 @foo(i32 %r1, i32 %r2, i32 %r3, i32 %r4, i32 %r5, i32 %r6, i32 %r7, i32 %r8, i32 %r9, i32 %r10, i32 %r11, i32 %r12, i32 %r13, i32 %r14) {
    entry:
        %r15 = mul i32 2, %r1
        %r16 = sdiv i32 %r2, 2
        %r17 = sdiv i32 %r10, 2
        %r18 = add i32 %r13, %r14
        %r19 = add i32 %r12, %r18
        %r20 = add i32 %r11, %r19
        %r21 = add i32 %r17, %r20
        %r22 = add i32 %r9, %r21
        %r23 = add i32 %r8, %r22
        %r24 = add i32 %r7, %r23
        %r25 = add i32 %r6, %r24
        %r26 = add i32 %r5, %r25
        %r27 = add i32 %r4, %r26
        %r28 = add i32 %r3, %r27
        %r29 = add i32 %r16, %r28
        %r30 = add i32 %r15, %r29
        %r31 = srem i32 %r30, 10
                                                                                                    ;r = (((2) * (a)) + (((b) / (2)) + ((c) + ((d) + ((e) + ((f) + ((g) + ((h) + ((i) + (((j) / (2)) + ((k) + ((l) + ((m) + (n)))))))))))))) % (10)
                                                                                                    ;r ~ %r31
        call void @printInt(i32 %r31)
        ret i32 %r31
}
