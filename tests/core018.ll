declare void @printInt(i32)
declare void @printString(i8*)
declare void @error()
declare i32 @readInt()
declare i8* @readString()
declare i8* @.strconcat(i8*, i8*)
declare i1 @.strcompare(i8*, i8*)









define i32 @main() {
    entry:
        %r0 = call i32 @readInt()
                                                                                                    ;x = readInt()
                                                                                                    ;x ~ %r0
        %r1 = call i8* @readString()
                                                                                                    ;y = readString()
                                                                                                    ;y ~ %r1
        %r2 = call i8* @readString()
                                                                                                    ;z = readString()
                                                                                                    ;z ~ %r2
        %r3 = sub i32 %r0, 5
        call void @printInt(i32 %r3)
        %r5 = call i8* @.strconcat(i8* %r1, i8* %r2)
        call void @printString(i8* %r5)
        ret i32 0
}
