# MSIX 打包说明

## 已准备好的文件

以下文件已同步到 GitHub 仓库 (https://github.com/Wadeonetest/zbtipfree):

✅ 必需的图标文件 (Assets文件夹)
✅ 主程序 (live_recorder_sprite.py)
✅ PyInstaller spec文件 (直播录屏标记精灵.spec)
✅ 图标创建脚本 (create_icons.py)

## MSIX包需要的所有图标

| 图标文件 | 尺寸 | 用途 |
|---------|------|------|
| Square44x44Logo.png | 44x44 | 应用商店中显示 |
| Square71x71Logo.png | 71x71 | 小磁贴 |
| Square150x150Logo.png | 150x150 | 中磁贴 |
| Square310x310Logo.png | 310x310 | 大磁贴 |
| Wide310x150Logo.png | 310x150 | 宽磁贴 |
| StoreLogo.png | 50x50 | 商店Logo |
| SplashScreen.png | 620x300 | 启动画面 |
| SmallTile.png | 71x71 | 小磁贴(备用) |

## 使用 MSIX Packaging Tool 重新打包的步骤

### 方法 1: 使用现有模板更新 (推荐)

1. 从 GitHub 下载最新代码，确保 Assets 文件夹包含所有图标
2. 打开 MSIX Packaging Tool
3. 选择 "修改现有包"
4. 选择你之前创建的 "直播录屏标记精灵.msix"
5. 在包编辑器中：
   - 找到 "Assets" 文件夹
   - 替换或添加所有缺失的图标文件
   - 确保 AppxManifest.xml 中的图标引用正确
6. 重新保存并签名

### 方法 2: 全新打包

1. 准备：确保你有完整的发布文件夹
   ```
   free1.0.1/
   ├── dist/
   │   └── 直播录屏标记精灵/      # PyInstaller打包好的文件夹
   └── Assets/                      # 所有必需的图标文件
   ```

2. 使用 MSIX Packaging Tool 进行打包

3. 在创建包的过程中，确保将 Assets 文件夹包含在包的根目录

4. 在 AppxManifest.xml 中添加正确的图标引用

## AppxManifest.xml 示例配置

以下是正确的 VisualElements 配置，你可以参考：

```xml
<Applications>
  <Application Id="App" 
               Executable="直播录屏标记精灵.exe" 
               EntryPoint="Windows.FullTrustApplication">
    <uap:VisualElements
      DisplayName="直播录屏标记精灵"
      Description="直播录屏标记精灵"
      BackgroundColor="transparent"
      Square150x150Logo="Assets\Square150x150Logo.png"
      Square44x44Logo="Assets\Square44x44Logo.png">
      <uap:DefaultTile 
        Square310x310Logo="Assets\Square310x310Logo.png"
        Wide310x150Logo="Assets\Wide310x150Logo.png"
        Square71x71Logo="Assets\Square71x71Logo.png"/>
      <uap:SplashScreen Image="Assets\SplashScreen.png"/>
    </uap:VisualElements>
  </Application>
</Applications>
```

## 重新生成图标（如果需要）

如果需要重新生成图标，可以运行：

```bash
cd D:\代码存档\zbtip\free1.0.1
python create_icons.py
```

这会在 Assets 文件夹中重新生成所有必需的图标。

## 重要提示

1. **所有图标都必需**：应用商店会验证所有必需的图标是否存在
2. **文件名要精确**：文件名必须与 AppxManifest.xml 中引用的一致
3. **文件夹结构**：Assets 文件夹必须在 MSIX 包的根目录
4. **同步代码**：每次修改代码后，先运行 PyInstaller 打包，然后再用 MSIX Packaging Tool 打包

## 常见问题

**Q: 商店仍然报错说找不到图标？**

A: 请检查：
- MSIX 包中是否真的包含了所有图标文件（可以用7zip解压MSIX检查）
- 图标文件名是否与 AppxManifest.xml 中引用的完全一致（大小写也要注意）
- 图标是否在正确的 Assets 文件夹中
