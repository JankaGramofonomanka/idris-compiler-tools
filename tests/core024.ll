declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s0 = internal constant [4 x i8] c"yes\00"
@s1 = internal constant [5 x i8] c"NOOO\00"





define i32 @main() {
    entry:
        call void @f(i32 1, i32 2)
        ret i32 0
}

define void @f(i32 %r1, i32 %r2) {
    entry:
        %r3 = icmp sgt i32 %r2, %r1
        br i1 %r3, label %L1, label %L2
    L2:
        %r4 = call i1 @e()
        br i1 %r4, label %L1, label %L0
    L1:
        %r5 = getelementptr [4 x i8], [4 x i8]* @s0, i32 0, i32 0
        call void @printString(i8* %r5)
        br label %L0
    L0:
        ret void
}

define i1 @e() {
    entry:
        %r7 = getelementptr [5 x i8], [5 x i8]* @s1, i32 0, i32 0
        call void @printString(i8* %r7)
        ret i1 0
}
