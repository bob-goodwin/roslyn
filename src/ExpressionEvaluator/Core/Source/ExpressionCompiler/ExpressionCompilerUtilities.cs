﻿// Copyright (c) Microsoft.  All Rights Reserved.  Licensed under the Apache License, Version 2.0.  See License.txt in the project root for license information.

using System;

namespace Microsoft.CodeAnalysis.ExpressionEvaluator
{
    internal static class ExpressionCompilerUtilities
    {
        internal static string GenerateUniqueName()
        {
            return Guid.NewGuid().ToString("N");
        }
    }
}
