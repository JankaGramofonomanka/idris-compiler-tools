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
        call void @foo()
        ret i32 0
}

define void @foo() {
    entry:
        %r1 = getelementptr [4 x i8], [4 x i8]* @s0, i32 0, i32 0
        call void @printString(i8* %r1)
        ret void
}
