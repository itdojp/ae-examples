// WCAG 2.1 AA準拠のアクセシビリティユーティリティ

// 色のコントラスト比の計算（WCAG 2.1準拠）
export function calculateContrastRatio(color1: string, color2: string): number {
  // RGB値の正規化とルミナンス計算
  function getLuminance(color: string): number {
    // 16進数カラーコードをRGB値に変換
    const hex = color.replace('#', '');
    const r = parseInt(hex.substr(0, 2), 16) / 255;
    const g = parseInt(hex.substr(2, 2), 16) / 255;
    const b = parseInt(hex.substr(4, 2), 16) / 255;
    
    // sRGB値を線形RGB値に変換
    const rsRGB = r <= 0.03928 ? r / 12.92 : Math.pow((r + 0.055) / 1.055, 2.4);
    const gsRGB = g <= 0.03928 ? g / 12.92 : Math.pow((g + 0.055) / 1.055, 2.4);
    const bsRGB = b <= 0.03928 ? b / 12.92 : Math.pow((b + 0.055) / 1.055, 2.4);
    
    // 相対輝度の計算
    return 0.2126 * rsRGB + 0.7152 * gsRGB + 0.0722 * bsRGB;
  }
  
  const luminance1 = getLuminance(color1);
  const luminance2 = getLuminance(color2);
  
  const lighter = Math.max(luminance1, luminance2);
  const darker = Math.min(luminance1, luminance2);
  
  return (lighter + 0.05) / (darker + 0.05);
}

// WCAG AA準拠のコントラストチェック
export function checkContrastRatio(
  foreground: string,
  background: string,
  isLargeText: boolean = false
): {
  ratio: number;
  passAA: boolean;
  passAAA: boolean;
  recommendation?: string;
} {
  const ratio = calculateContrastRatio(foreground, background);
  const minRatioAA = isLargeText ? 3 : 4.5;
  const minRatioAAA = isLargeText ? 4.5 : 7;
  
  const passAA = ratio >= minRatioAA;
  const passAAA = ratio >= minRatioAAA;
  
  let recommendation: string | undefined;
  if (!passAA) {
    if (isLargeText) {
      recommendation = 'Large text requires a minimum contrast ratio of 3:1 for WCAG AA compliance.';
    } else {
      recommendation = 'Normal text requires a minimum contrast ratio of 4.5:1 for WCAG AA compliance.';
    }
  }
  
  return { ratio, passAA, passAAA, recommendation };
}

// ARIAラベルの生成
export function generateAriaLabel(
  text: string,
  context?: string,
  additionalInfo?: string[]
): string {
  let label = text.trim();
  
  if (context) {
    label = `${context}: ${label}`;
  }
  
  if (additionalInfo && additionalInfo.length > 0) {
    label += `, ${additionalInfo.join(', ')}`;
  }
  
  return label;
}

// フォーカス管理のユーティリティ
export class FocusManager {
  private focusStack: HTMLElement[] = [];
  
  // フォーカスのトラップ（モーダルダイアログ等で使用）
  trapFocus(container: HTMLElement): void {
    const focusableElements = container.querySelectorAll(
      'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
    );
    const firstElement = focusableElements[0] as HTMLElement;
    const lastElement = focusableElements[focusableElements.length - 1] as HTMLElement;
    
    container.addEventListener('keydown', (e) => {
      if (e.key === 'Tab') {
        if (e.shiftKey) {
          if (document.activeElement === firstElement) {
            e.preventDefault();
            lastElement.focus();
          }
        } else {
          if (document.activeElement === lastElement) {
            e.preventDefault();
            firstElement.focus();
          }
        }
      }
    });
    
    // 初期フォーカスの設定
    firstElement?.focus();
  }
  
  // フォーカス位置の保存
  saveFocus(): void {
    const activeElement = document.activeElement as HTMLElement;
    if (activeElement) {
      this.focusStack.push(activeElement);
    }
  }
  
  // フォーカス位置の復元
  restoreFocus(): void {
    const element = this.focusStack.pop();
    if (element && typeof element.focus === 'function') {
      element.focus();
    }
  }
}

// スクリーンリーダー向けのライブリージョン管理
export class LiveRegionAnnouncer {
  private politeRegion: HTMLElement;
  private assertiveRegion: HTMLElement;
  
  constructor() {
    // polite（丁寧）な通知用リージョン
    this.politeRegion = document.createElement('div');
    this.politeRegion.setAttribute('aria-live', 'polite');
    this.politeRegion.setAttribute('aria-atomic', 'true');
    this.politeRegion.style.position = 'absolute';
    this.politeRegion.style.left = '-10000px';
    this.politeRegion.style.width = '1px';
    this.politeRegion.style.height = '1px';
    this.politeRegion.style.overflow = 'hidden';
    document.body.appendChild(this.politeRegion);
    
    // assertive（強制的）な通知用リージョン
    this.assertiveRegion = document.createElement('div');
    this.assertiveRegion.setAttribute('aria-live', 'assertive');
    this.assertiveRegion.setAttribute('aria-atomic', 'true');
    this.assertiveRegion.style.position = 'absolute';
    this.assertiveRegion.style.left = '-10000px';
    this.assertiveRegion.style.width = '1px';
    this.assertiveRegion.style.height = '1px';
    this.assertiveRegion.style.overflow = 'hidden';
    document.body.appendChild(this.assertiveRegion);
  }
  
  // 丁寧な通知（ユーザーの操作を中断しない）
  announcePolitely(message: string): void {
    this.politeRegion.textContent = message;
  }
  
  // 強制的な通知（緊急時・エラー時）
  announceAssertively(message: string): void {
    this.assertiveRegion.textContent = message;
  }
  
  // クリーンアップ
  destroy(): void {
    if (this.politeRegion.parentNode) {
      this.politeRegion.parentNode.removeChild(this.politeRegion);
    }
    if (this.assertiveRegion.parentNode) {
      this.assertiveRegion.parentNode.removeChild(this.assertiveRegion);
    }
  }
}

// キーボードナビゲーション支援
export function enhanceKeyboardNavigation(element: HTMLElement): void {
  // Enterキーでクリックイベントをトリガー
  element.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && element.getAttribute('role') === 'button') {
      e.preventDefault();
      element.click();
    }
  });
  
  // 矢印キーによるナビゲーション（リストやメニュー）
  if (element.getAttribute('role') === 'menu' || element.getAttribute('role') === 'listbox') {
    element.addEventListener('keydown', (e) => {
      const items = element.querySelectorAll('[role="menuitem"], [role="option"]');
      const currentIndex = Array.from(items).indexOf(document.activeElement as Element);
      let nextIndex = currentIndex;
      
      switch (e.key) {
        case 'ArrowDown':
          e.preventDefault();
          nextIndex = currentIndex < items.length - 1 ? currentIndex + 1 : 0;
          break;
        case 'ArrowUp':
          e.preventDefault();
          nextIndex = currentIndex > 0 ? currentIndex - 1 : items.length - 1;
          break;
        case 'Home':
          e.preventDefault();
          nextIndex = 0;
          break;
        case 'End':
          e.preventDefault();
          nextIndex = items.length - 1;
          break;
      }
      
      if (nextIndex !== currentIndex) {
        (items[nextIndex] as HTMLElement).focus();
      }
    });
  }
}

// 動的コンテンツのアクセシビリティ確保
export function announceContentChange(
  message: string,
  priority: 'polite' | 'assertive' = 'polite'
): void {
  if (typeof window !== 'undefined') {
    const announcer = new LiveRegionAnnouncer();
    
    if (priority === 'assertive') {
      announcer.announceAssertively(message);
    } else {
      announcer.announcePolitely(message);
    }
    
    // 5秒後にクリーンアップ
    setTimeout(() => {
      announcer.destroy();
    }, 5000);
  }
}

// 高コントラストモードの検出
export function detectHighContrastMode(): boolean {
  if (typeof window !== 'undefined') {
    // Windows High Contrast Modeの検出
    const testElement = document.createElement('div');
    testElement.style.borderWidth = '1px';
    testElement.style.borderStyle = 'solid';
    testElement.style.borderColor = 'red green';
    testElement.style.position = 'absolute';
    testElement.style.left = '-999px';
    document.body.appendChild(testElement);
    
    const styles = window.getComputedStyle(testElement);
    const isHighContrast = styles.borderTopColor === styles.borderRightColor;
    
    document.body.removeChild(testElement);
    return isHighContrast;
  }
  
  return false;
}

// 画像の代替テキスト検証
export function validateImageAlt(alt: string, context: string): {
  isValid: boolean;
  suggestions: string[];
} {
  const suggestions: string[] = [];
  
  if (!alt || alt.trim().length === 0) {
    return {
      isValid: false,
      suggestions: ['Provide meaningful alternative text that describes the image content or function.'],
    };
  }
  
  // 冗長な表現のチェック
  const redundantPhrases = ['image of', 'picture of', 'photo of', 'graphic of'];
  const hasRedundantPhrase = redundantPhrases.some(phrase => 
    alt.toLowerCase().includes(phrase)
  );
  
  if (hasRedundantPhrase) {
    suggestions.push('Avoid redundant phrases like "image of" or "picture of" in alt text.');
  }
  
  // 長さのチェック
  if (alt.length > 125) {
    suggestions.push('Consider shortening alt text to 125 characters or less, or use a longer description.');
  }
  
  // ファイル名のチェック
  if (alt.match(/\.(jpg|jpeg|png|gif|svg|webp)$/i)) {
    suggestions.push('Alt text appears to be a filename. Provide descriptive text instead.');
  }
  
  return {
    isValid: suggestions.length === 0,
    suggestions,
  };
}