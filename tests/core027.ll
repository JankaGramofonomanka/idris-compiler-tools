declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)




@s1 = internal constant [5 x i8] c"good\00"
@s0 = internal constant [4 x i8] c"bad\00"





define i32 @main() {
    entry:
        %r0 = getelementptr [4 x i8], [4 x i8]* @s0, i32 0, i32 0
        call void @f(i8* %r0)
        ret i32 0
}

define void @f(i8* %r2) {
    entry:
        %r3 = getelementptr [5 x i8], [5 x i8]* @s1, i32 0, i32 0
                                                                                                    ;arg = "good"
                                                                                                    ;arg ~ %r3
        call void @printString(i8* %r3)
        ret void
}
