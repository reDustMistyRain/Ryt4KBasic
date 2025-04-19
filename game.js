"use strict";
console.log("遊戲腳本開始執行...");

// =============================================================================
// DOM 元素獲取與檢查
// =============================================================================
const appContainer = document.getElementById('app-container');
const splashScreen = document.getElementById('splash-screen');
const songSelectScreen = document.getElementById('song-select-screen');
const songListContainer = document.getElementById('song-list-container');
const resultScreen = document.getElementById('result-screen');
const introScreen = document.getElementById('intro-screen');
const introIllustration = document.getElementById('intro-illustration');
const introTitle = document.getElementById('intro-title');
const introArtist = document.getElementById('intro-artist');
const resultIllustration = document.getElementById('result-illustration');
const resultTitle = document.getElementById('result-title');
const resultArtist = document.getElementById('result-artist');
const canvas = document.getElementById('gameCanvas');
const ctx = canvas.getContext('2d');
const speedDisplay = document.getElementById('speed-display');
const increaseSpeedButton = document.getElementById('increase-speed');
const decreaseSpeedButton = document.getElementById('decrease-speed');

if (!canvas || !ctx || !appContainer || !splashScreen || !songSelectScreen || !songListContainer || !resultScreen || !introScreen || !introIllustration || !introTitle || !introArtist || !resultIllustration || !resultTitle || !resultArtist || !speedDisplay || !increaseSpeedButton || !decreaseSpeedButton) {
    console.error("錯誤：無法找到必要的 HTML 元素！請確保 index.html 包含所有需要的 ID。");
    alert("頁面初始化錯誤！缺少必要的元素。");
    throw new Error("Missing critical HTML elements.");
}

// =============================================================================
// 遊戲狀態管理
// =============================================================================
let gameState = 'SPLASH';
let availableSongs = [];
let selectedSongData = null;
let gameStartDelayTimeoutId = null;

// =============================================================================
// 遊戲核心參數與設定
// =============================================================================
const LANE_COUNT = 4; let JUDGMENT_LINE_Y = 0; let PERSPECTIVE_STRENGTH = 0.8;
let TOP_TOTAL_WIDTH = 0; let TOP_OFFSET_X = 0; let BOTTOM_LANE_WIDTH = 0; let TOP_LANE_WIDTH = 0;
const START_DELAY_SECONDS = 0.1;
const INTRO_TO_GAME_DELAY_SECONDS = 2.0;
const BASE_NOTE_APPEAR_TIME_OFFSET = 2.0 / 3.0; // 音符從頂部到底部的預計時間偏移 (到判定線的時間)
let speedMultiplier = 1.0;
// 音符實際在屏幕上運動的時間長度 (從出現到判定線)
let noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier;
const MIN_SPEED_MULTIPLIER = 0.5;
const MAX_SPEED_MULTIPLIER = 5.0;
const SPEED_ADJUST_STEP = 0.25;
const NOTE_HEIGHT_RATIO = 0.03; let NOTE_HEIGHT = 20; // 音符在判定線處的基礎高度
const NOTE_SPEED_EASING_POWER = 2.0; // 使用者調整後的值
const LINEAR_MIX_FACTOR = 0.25;      // 使用者調整後的值

// =============================================================================
// 字體設定
// =============================================================================
const FONT_FAMILY_CANVAS = "'IBM Plex Mono', monospace";

// =============================================================================
// 顏色定義
// =============================================================================
const COLOR_BACKGROUND = '#000000';
const COLOR_LINES = '#FFFFFF'; const COLOR_LANE_SEPARATOR = '#CCCCCC';
const COLOR_JUDGMENT_LINE = '#FFFFFF'; // 白色判定線
const COLOR_NOTE = '#CCFFFF';
const COLOR_PERFECT_PARTICLE = 'rgba(255, 215, 0,';
const COLOR_GREAT_PARTICLE = 'rgba(144, 238, 144,';
const COLOR_GOOD_PARTICLE = 'rgba(173, 216, 230,';
const COLOR_LANE_FLASH = 'rgba(173, 216, 230,'; // 淺藍色軌道閃爍
const COLOR_RING_EFFECT = 'rgba(255, 255, 255,';
const COLOR_SHOCKWAVE_PERFECT = 'rgba(255, 215, 0,';
const COLOR_SHOCKWAVE_GREAT = 'rgba(144, 238, 144,';
const COLOR_SHOCKWAVE_GOOD = 'rgba(173, 216, 230,';
const COLOR_JUDGMENT_LINE_PULSE = 'rgba(255, 255, 255,';
// 垂直光束特效顏色常量
const COLOR_LANE_BEAM = 'rgba(180, 210, 255,'; // 柔和的藍白色光束
const COLOR_BEAM_GLOW = 'rgba(180, 210, 255, 0.001)'; // 光束發光顏色

// =============================================================================
// 判定與計分系統 (1 Million Score System)
// =============================================================================
const JUDGE_WINDOW_PERFECT = 0.100; const JUDGE_WINDOW_GREAT = 0.200; const JUDGE_WINDOW_GOOD = 0.300; const JUDGE_WINDOW_MISS = 0.400;
let lastJudgment = { text: '', time: 0, column: -1 }; const JUDGMENT_DISPLAY_DURATION = 0.5;
let score = 0; let combo = 0; let maxCombo = 0;
const MAX_SCORE = 1000000;
let totalNotesInChart = 0; let baseScorePerPerfect = 0;
let judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };

// =============================================================================
// 按鍵與音訊狀態
// =============================================================================
const KEY_MAPPINGS = ['KeyD', 'KeyF', 'KeyJ', 'KeyK']; const keyStates = {'KeyD': false, 'KeyF': false, 'KeyJ': false, 'KeyK': false};
const AudioContext = window.AudioContext || window.webkitAudioContext; let audioContext; let audioBuffer = null; let audioSource = null;
let audioStartTime = 0; let currentSongTime = 0; let rawElapsedTime = -START_DELAY_SECONDS; // 遊戲內時間從 -START_DELAY_SECONDS 開始
let isAudioLoading = false; let isAudioReady = false; let isPlaying = false; let gameLoopRunning = false;

// Keysound
let keysoundBuffer = null; let isKeysoundLoading = false; let isKeysoundReady = false;
const KEYSOUND_PATH = 'assets/beat.wav'; const KEYSOUND_VOLUME = 0.3;

// =============================================================================
// 譜面數據
// =============================================================================
let chartData = null; let loadedNotes = []; let globalOffsetSeconds = 0;
let isChartLoading = false; let isChartReady = false;

// =============================================================================
// 背景圖相關
// =============================================================================
let songBgImage = null; let isSongBgLoading = false; let isSongBgReady = false;
const BACKGROUND_BLUR_AMOUNT = 5; const BACKGROUND_DIM_ALPHA = 0.7;

// =============================================================================
// 特效相關
// =============================================================================
let activeHitEffects = []; let activeLaneFlashes = []; let activeRingEffects = [];
let activeShockwaves = []; let activeJudgmentLinePulses = [];
// 垂直光束特效列表
let activeLaneBeams = [];

// Particle params
const PARTICLE_COUNT_PERFECT = 12; const PARTICLE_COUNT_GREAT = 8; const PARTICLE_COUNT_GOOD = 5;
const PARTICLE_BASE_SPEED = 100; const PARTICLE_RANDOM_SPEED = 100;
const PARTICLE_BASE_SIZE = 40; const PARTICLE_RANDOM_SIZE = 10;
const PARTICLE_MIN_LIFETIME = 0.3; const PARTICLE_MAX_LIFETIME = 0.6;
const PARTICLE_ANGULAR_VELOCITY_RANGE = Math.PI * 2;
// Lane flash params
const LANE_FLASH_DURATION = 0;
// Ring effect params
const RING_EFFECT_DURATION = 0.3;
const RING_EFFECT_START_SCALE = 0.15; // 使用者調整後的值
const RING_EFFECT_END_SCALE = 1.0;   // 使用者調整後的值
const RING_EFFECT_LINE_WIDTH = 3;
const RING_GLOW_BLUR = 10;
const RING_GLOW_COLOR = 'rgba(255, 255, 255, 0.5)';
// Shockwave params
const SHOCKWAVE_DURATION = 0.2;
const SHOCKWAVE_START_SCALE = 0.1;
const SHOCKWAVE_END_SCALE = 2.5;
// Judgment line pulse params
const JUDGMENT_LINE_PULSE_DURATION = 0.15;
const JUDGMENT_LINE_PULSE_MAX_WIDTH_MULTIPLIER = 2.0;
const JUDGMENT_LINE_PULSE_MAX_ALPHA = 1.0;
// 垂直光束特效參數
const BEAM_DURATION = 1.0; // 光束持續時間
const BEAM_GLOW_BLUR = 20; // 光束發光模糊度
// 注意：BEAM_WIDTH_MULTIPLIER 不再需要，光束寬度直接等於判定線處軌道寬度

// =============================================================================
// 遊戲內小曲繪狀態
// =============================================================================
let gameInfoIllustration = null;
let gameInfoIllustrationSrc = '';
let gameInfoIllustrationLoaded = false;

// =============================================================================
// Easing 函數
// =============================================================================
function easeOutCubic(t) { return 1 - Math.pow(1 - t, 3); }
function easeInOutQuad(t) { return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2; }
function easePulseSine(t) { return Math.sin(t * Math.PI); }

// =============================================================================
// 初始化與狀態重置
// =============================================================================
function initializeGameState() {
    // 重置所有音符的狀態，確保遊戲開始時所有音符都是未判定且未活躍的
    loadedNotes.forEach(note => {
        note.isActive = false; // <--- 確保這個被重置 (用於控制繪製和移動)
        note.y = 0;
        note.judged = false;
        note.judgment = '';
    });

    score = 0; combo = 0; maxCombo = 0;
    lastJudgment = { text: '', time: 0, column: -1 };
    judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };

    // 清空所有特效列表
    activeHitEffects = [];
    activeLaneFlashes = [];
    activeRingEffects = [];
    activeShockwaves = [];
    activeJudgmentLinePulses = [];
    activeLaneBeams = []; // 清空垂直光束特效列表

    // **修改點：移除遊戲內小曲繪和背景圖狀態的重置**
    // 這些狀態應該在返回選單或載入新圖時管理，而不是在遊戲開始時重置
    // songBgImage = null; isSongBgLoading = false; isSongBgReady = false;
    // gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;

    // 取消遊戲開始延遲定時器
    if (gameStartDelayTimeoutId) {
        clearTimeout(gameStartDelayTimeoutId);
        gameStartDelayTimeoutId = null;
    }
    console.log("遊戲狀態變數已重置 (分數, 連擊, 判定計數, 特效等)。");
}

// =============================================================================
// 輔助函式
// =============================================================================
// 根據透視效果，計算在特定Y座標處的X座標 (用於繪製軌道和音符)
function getInterpolatedX(boundaryIndex, y) {
    if (BOTTOM_LANE_WIDTH === undefined || TOP_LANE_WIDTH === undefined || TOP_OFFSET_X === undefined || canvas.height <= 0) return 0;

    const bottomX = boundaryIndex * BOTTOM_LANE_WIDTH;
    const topX = TOP_OFFSET_X + (boundaryIndex * TOP_LANE_WIDTH);

    // 計算在 clampedY 位置時，Y在0到canvas.height之間的比例
    // 允許 Y 超出範圍，以處理音符滑出屏幕的情況
    const ratio = canvas.height > 0 ? (y / canvas.height) : 0;

     // 在頂部和底部X之間進行線性插值
     // ratio = 0 (y=0) 時返回 topX
     // ratio = 1 (y=canvas.height) 時返回 bottomX
    return topX + (bottomX - topX) * ratio;
}

function resizeCanvas() {
    const displayWidth = window.innerWidth;
    const displayHeight = window.innerHeight;

    // 僅在實際尺寸變化較大時才重新設置 canvas 大小和計算參數
    if (Math.abs(canvas.width - displayWidth) > 1 || Math.abs(canvas.height - displayHeight) > 1) {
        canvas.width = displayWidth;
        canvas.height = displayHeight;
        console.log(`Canvas resized to: ${canvas.width} x ${canvas.height}`);

        // 重新計算遊戲相關參數
        JUDGMENT_LINE_Y = canvas.height * 0.85; // 判定線位置
        PERSPECTIVE_STRENGTH = 0.8; // 確保這個值是常量或在resize時重新獲取
        TOP_TOTAL_WIDTH = canvas.width * (1 - PERSPECTIVE_STRENGTH); // 軌道在頂部的總寬度
        TOP_OFFSET_X = (canvas.width - TOP_TOTAL_WIDTH) / 2; // 軌道頂部左側的偏移
        BOTTOM_LANE_WIDTH = canvas.width / LANE_COUNT; // 軌道在底部的每軌寬度
        TOP_LANE_WIDTH = TOP_TOTAL_WIDTH / LANE_COUNT; // 軌道在頂部的每軌寬度
        NOTE_HEIGHT = Math.max(10, Math.round(canvas.height * NOTE_HEIGHT_RATIO)); // 音符基礎高度

        console.log(`重新計算參數: 判定線 Y=${JUDGMENT_LINE_Y.toFixed(0)}, 音符基礎高度=${NOTE_HEIGHT}, TOP_TOTAL_WIDTH=${TOP_TOTAL_WIDTH.toFixed(0)}`);

        // 如果不在遊戲中，重新繪製背景以適應新尺寸
        if (!gameLoopRunning && ctx && gameState !== 'LOADING' && gameState !== 'INITIALIZING' && gameState !== 'SELECTING' && gameState !== 'SPLASH') {
            drawGameBackground();
        }
    }
}

function drawGameBackground() {
    if (!ctx) return;

    ctx.clearRect(0, 0, canvas.width, canvas.height); // 清空畫布

    // 繪製背景圖 (如果已載入)
    if (isSongBgReady && songBgImage) {
        ctx.filter = `blur(${BACKGROUND_BLUR_AMOUNT}px)`; // 應用模糊濾鏡

        // 計算背景圖繪製尺寸和位置以覆蓋整個 canvas 並保持比例
        const canvasAspect = canvas.width / canvas.height;
        const bgAspect = songBgImage.naturalWidth / songBgImage.naturalHeight;
        let drawWidth, drawHeight, offsetX = 0, offsetY = 0;

        if (bgAspect > canvasAspect) {
            // 背景圖比 canvas 寬，高度匹配 canvas，寬度裁剪
            drawHeight = canvas.height;
            drawWidth = drawHeight * bgAspect;
            offsetX = (canvas.width - drawWidth) / 2; // 居中
        } else {
            // 背景圖比 canvas 高，寬度匹配 canvas，高度裁剪
            drawWidth = canvas.width;
            drawHeight = drawWidth / bgAspect;
            offsetY = (canvas.height - drawHeight) / 2; // 居中
        }

        try {
            ctx.drawImage(songBgImage, offsetX, offsetY, drawWidth, drawHeight);
        } catch (e) {
            console.error("繪製背景圖時出錯:", e);
            // 繪製失敗則清除狀態，回退到純黑背景
            isSongBgReady = false;
            songBgImage = null;
            ctx.filter = 'none'; // 繪製錯誤背景前移除濾鏡
            ctx.fillStyle = COLOR_BACKGROUND;
            ctx.fillRect(0, 0, canvas.width, canvas.height);
        }

        ctx.filter = 'none'; // 移除濾鏡

        // 繪製變暗疊加層
        ctx.fillStyle = `rgba(0, 0, 0, ${BACKGROUND_DIM_ALPHA})`;
        ctx.fillRect(0, 0, canvas.width, canvas.height);
    } else {
        // 如果背景圖未載入或載入失敗，使用純黑背景
        ctx.fillStyle = COLOR_BACKGROUND;
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        // 如果背景圖未載入且應該有背景圖 (遊戲或載入狀態)，嘗試觸發載入
        if (!isSongBgLoading && !isSongBgReady && selectedSongData?.illustrationPath && (gameState === 'LOADING' || gameState === 'GAME' || gameState === 'PLAYING')) {
            loadSongBackgroundImage(selectedSongData.illustrationPath);
        }
    }

    // 在遊戲或播放狀態下才繪製靜態透視元素 (軌道線、判定線)
    if (gameState === 'GAME' || gameState === 'PLAYING') {
        drawPerspectiveStaticElements();
    }
}

// =============================================================================
// UI 畫面管理與更新
// =============================================================================
function showScreen(screenId) {
    const allOverlays = [splashScreen, songSelectScreen, resultScreen, introScreen];
    let targetOverlayScreen = null;
    let previousState = gameState;
    console.log(`[showScreen] 嘗試切換到畫面: ${screenId}`);

    // 隱藏所有疊加畫面
    allOverlays.forEach(screen => {
         screen.classList.add('hidden');
         screen.classList.remove('visible'); // 確保移除 visible 類，以便下次能觸發過渡
         screen.style.opacity = 0; // 強制設置透明，以便 hidden 移除後 opacity 過渡能正常工作
    });


    // 處理 Canvas 的顯示
    if (screenId === 'GAME' || screenId === 'PLAYING') { // GAME和PLAYING狀態下Canvas可見
        canvas.classList.remove('hidden');
        console.log("[showScreen] Canvas 設為可見");
    } else {
        canvas.classList.add('hidden');
        console.log(`[showScreen] Canvas 設為隱藏 (狀態: ${screenId})`);
    }

    // 根據目標狀態設置目標疊加畫面並執行清理
    switch (screenId) {
        case 'SPLASH':
            targetOverlayScreen = splashScreen;
            break;
        case 'SELECTING':
            targetOverlayScreen = songSelectScreen;
            // 返回選單時，停止所有遊戲相關活動並清理資源
            if (isPlaying || gameLoopRunning || gameStartDelayTimeoutId) {
                console.log("返回選單，執行遊戲清理...");
                if (audioSource) {
                    try { audioSource.stop(); } catch(e){ console.warn("停止舊音源時出錯(可能已停止):", e); }
                    audioSource.disconnect();
                    audioSource = null;
                }
                isPlaying = false;
                gameLoopRunning = false;
                if (gameStartDelayTimeoutId) {
                    clearTimeout(gameStartDelayTimeoutId);
                    gameStartDelayTimeoutId = null;
                }
                // 重置遊戲相關數據
                loadedNotes = [];
                activeHitEffects = [];
                activeLaneFlashes = [];
                activeRingEffects = [];
                activeShockwaves = [];
                activeJudgmentLinePulses = [];
                activeLaneBeams = []; // 清空垂直光束特效
                isAudioReady = false;
                isChartReady = false;
                selectedSongData = null; // 清空選中的歌曲數據
                chartData = null;
                audioBuffer = null;
                // **修改點：在返回選單時，清除當前歌曲的背景圖和遊戲內曲繪狀態**
                songBgImage = null; isSongBgLoading = false; isSongBgReady = false;
                gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;
                totalNotesInChart = 0;
                baseScorePerPerfect = 0;
                score = 0; combo = 0; maxCombo = 0; // 重置結算數據
                judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 }; // 重置結算數據
                lastJudgment = { text: '', time: 0, column: -1 }; // 重置結算數據
                console.log("遊戲資源已清理。");
            }
            break;
        case 'RESULT':
            targetOverlayScreen = resultScreen;
             // 結算畫面不執行清理，保留數據供顯示 (包括 selectedSongData 和相關圖片狀態)
            break;
        case 'INTRO':
            targetOverlayScreen = introScreen;
             // Intro 畫面不執行清理，等待開始遊戲或返回
            break;
        case 'GAME':
        case 'PLAYING': // PLAYING 只是 GAME 狀態下音樂正在播放的子狀態
        case 'LOADING':
        case 'INITIALIZING': // 假設 INITIALIZING 是 APP 剛啟動的內部狀態，無特定畫面
            targetOverlayScreen = null; // 這些狀態下沒有疊加畫面
            break;
        default:
            console.error("未知的畫面 ID:", screenId);
            targetOverlayScreen = songSelectScreen; // 未知狀態回退到選曲畫面
            screenId = 'SELECTING';
            break;
    }

    gameState = screenId;
    console.log(`[showScreen] 狀態從 ${previousState} 切換到: ${gameState}`);


    if (targetOverlayScreen) {
        // 將目標疊加畫面設為可見 (移除 hidden)
        targetOverlayScreen.classList.remove('hidden');
        console.log(`[showScreen] ${targetOverlayScreen.id} 畫面已移除 hidden`);

        // 強制瀏覽器重繪，以便 opacity 過渡生效
        void targetOverlayScreen.offsetWidth;

        // 稍後添加 visible 類觸發過渡
        requestAnimationFrame(() => {
             // 使用一個小延遲確保移除 hidden 後有時間應用初始 opacity: 0
            setTimeout(() => {
                // 在添加 visible 前再次檢查狀態，防止在延遲期間狀態又變了
                if (gameState === screenId) {
                    targetOverlayScreen.classList.add('visible');
                    targetOverlayScreen.style.opacity = 1; // 顯式設置 opacity 確保兼容性
                    console.log(`[showScreen] ${targetOverlayScreen.id} (${screenId}) set to visible`);
                } else {
                    console.log(`[showScreen] State changed (${gameState}) before ${targetOverlayScreen.id} (${screenId}) could become visible.`);
                    // 如果狀態變了，可能需要重新處理這個畫面（例如，如果變成了另一個疊加畫面）
                    // 但在這裡簡單地不做任何事情，因為新的 showScreen 呼叫會處理
                }
            }, 50); // 50ms 的小延遲
        });
    } else {
        console.log(`[showScreen] ${screenId} 狀態，無特定疊加畫面。`);
    }

    // 在非遊戲狀態下，如果 Canvas 已經初始化，確保背景被繪製 (特別是resize後)
    if (screenId !== 'GAME' && screenId !== 'PLAYING' && ctx) {
         if (canvas.width === 0 || canvas.height === 0) resizeCanvas(); // 確保canvas尺寸正確
         drawGameBackground();
    }
}


function populateSongList() {
    if (!songListContainer) return;
    songListContainer.innerHTML = ''; // 清空現有列表

    if (availableSongs.length === 0) {
        songListContainer.innerHTML = '<p>未找到歌曲。</p>';
        return;
    }

    // 根據標題排序歌曲列表
    availableSongs.sort((a, b) => a.title.localeCompare(b.title));

    availableSongs.forEach(song => {
        const songItem = document.createElement('div');
        songItem.classList.add('song-item');
        // 將歌曲數據存儲在 dataset 中
        songItem.dataset.songId = song.id;
        songItem.dataset.chartPath = song.chartPath;
        songItem.dataset.audioPath = song.audioPath;
        songItem.dataset.illustrationPath = song.illustrationPath;
        songItem.dataset.title = song.title;
        songItem.dataset.artist = song.artist || '未知';

        const img = document.createElement('img');
        img.classList.add('song-illustration');
        img.src = song.illustrationPath;
        img.alt = song.title; // 使用歌曲標題作為 alt 文本
        img.onerror = () => {
             console.warn(`歌曲插圖載入失敗: ${song.illustrationPath}. 使用預設圖。`);
            img.src = 'placeholder.png'; // 載入失敗時使用預設圖
        };

        const details = document.createElement('div');
        details.classList.add('song-details');

        const titleP = document.createElement('p');
        titleP.classList.add('song-title');
        titleP.textContent = song.title;

        const artistP = document.createElement('p');
        artistP.classList.add('song-artist');
        artistP.textContent = song.artist || '未知'; // 如果沒有 artist 則顯示 '未知'

        details.appendChild(titleP);
        details.appendChild(artistP);

        songItem.appendChild(img);
        songItem.appendChild(details);

        // 添加點擊事件監聽器
        songItem.addEventListener('click', handleSongSelect);

        songListContainer.appendChild(songItem);
    });
}

// =============================================================================
// 資源載入與狀態檢查
// =============================================================================
async function loadAudio(url) {
    if (!url) { console.error("音訊路徑無效！"); isAudioLoading = false; isAudioReady = false; updateLoadingStatus(); return; }
    if (!audioContext) { console.error("AudioContext 未初始化！無法載入音訊。"); isAudioLoading = false; isAudioReady = false; updateLoadingStatus(); return; }
    if (isAudioLoading || isAudioReady) { console.log("音訊正在載入或已載入，跳過重複載入。"); return; }
    isAudioLoading = true;
    isAudioReady = false;
    audioBuffer = null;
    updateLoadingStatus();
    console.log(`載入音訊: ${url}...`);
    try {
        const response = await fetch(url);
        if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
        const arrayBuffer = await response.arrayBuffer();
        audioBuffer = await audioContext.decodeAudioData(arrayBuffer);
        isAudioReady = true;
        console.log("歌曲音訊載入完成！");
    } catch (error) {
        console.error(`載入音訊錯誤 (${url}):`, error);
        alert(`載入歌曲音訊失敗: ${url}\n${error.message}`);
        // 載入失敗，返回選曲畫面
        showScreen('SELECTING');
    } finally {
        isAudioLoading = false;
        updateLoadingStatus();
        // 不論成功或失敗，都檢查是否可以觸發 Intro
        checkAndTriggerIntro();
    }
}

async function loadChart(url) {
     if (!url) { console.error("譜面路徑無效！"); isChartLoading = false; isChartReady = false; updateLoadingStatus(); return; }
    if (isChartLoading || isChartReady) { console.log("譜面正在載入或已載入，跳過重複載入。"); return; }
    isChartLoading = true;
    isChartReady = false;
    chartData = null;
    loadedNotes = []; // 清空舊的音符列表
    totalNotesInChart = 0;
    baseScorePerPerfect = 0;
    updateLoadingStatus();
    console.log(`載入譜面: ${url}...`);
    try {
        const response = await fetch(url);
        if (!response.ok) throw new Error(`無法載入譜面: ${response.statusText}`);
        chartData = await response.json();

        if (!chartData || !Array.isArray(chartData.notes) || !chartData.metadata) {
            throw new Error("譜面格式錯誤：缺少 notes 陣列或 metadata 物件。");
        }

        globalOffsetSeconds = (chartData.metadata.global_offset_ms || 0) / 1000.0;
        loadedNotes = [];
        // 過濾並處理音符數據
        chartData.notes.forEach((note, index) => {
            // 檢查必要的音符屬性
            if (note && typeof note.targetTime === 'number' && typeof note.column === 'number' && note.column >= 0 && note.column < LANE_COUNT) {
                 // 為每個音符添加一個唯一的 ID (這裡使用陣列索引作為簡易 ID)
                const noteId = note.id !== undefined ? note.id : `note_${index}`;
                const adjustedTargetTime = note.targetTime + globalOffsetSeconds;
                loadedNotes.push({
                    ...note, // 複製原始音符屬性
                    id: noteId, // 使用或生成 ID
                    originalTargetTime: note.targetTime, // 保存原始時間以便查錯/調試
                    targetTime: adjustedTargetTime, // 應用全局偏移後的時間
                    y: 0, // 初始 y 座標
                    judged: false, // 初始狀態為未判定
                    judgment: '', // 初始判定結果
                    isActive: false // <--- **新增/修改：初始標記為不活躍 (用於控制繪製和位置更新)**
                });
            } else {
                console.warn("忽略格式不符或無效的音符數據:", note);
            }
        });

        totalNotesInChart = loadedNotes.length;
        if (totalNotesInChart > 0) {
            baseScorePerPerfect = MAX_SCORE / totalNotesInChart;
            console.log(`譜面載入完成！共 ${totalNotesInChart} 音符。Perfect基礎分數: ${baseScorePerPerfect.toFixed(4)}`);
        } else {
            baseScorePerPerfect = 0;
            console.warn("譜面載入完成，但有效 Note 數量為 0！");
        }
        isChartReady = true;

    } catch (error) {
        console.error(`載入譜面錯誤 (${url}):`, error);
        alert(`載入譜面失敗: ${url}\n${error.message}`);
         // 載入失敗，返回選曲畫面
        showScreen('SELECTING');
        // 重置相關狀態
        chartData = null;
        loadedNotes = [];
        totalNotesInChart = 0;
        baseScorePerPerfect = 0;
        isChartReady = false;
    } finally {
        isChartLoading = false;
        updateLoadingStatus();
         // 不論成功或失敗，都檢查是否可以觸發 Intro
        checkAndTriggerIntro();
    }
}

async function loadKeysound() {
    if (!audioContext) { console.error("AudioContext 未初始化！無法載入打擊音效。"); isKeysoundLoading = false; isKeysoundReady = false; return; }
    if (isKeysoundLoading || isKeysoundReady) { console.log("打擊音效正在載入或已載入，跳過重複載入。"); return; }
    isKeysoundLoading = true;
    isKeysoundReady = false;
    keysoundBuffer = null;
    console.log(`載入打擊音效: ${KEYSOUND_PATH}...`);
    try {
        const response = await fetch(KEYSOUND_PATH);
        if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
        const arrayBuffer = await response.arrayBuffer();
        keysoundBuffer = await audioContext.decodeAudioData(arrayBuffer);
        isKeysoundReady = true;
        console.log("打擊音效載入完成！");
    } catch (error) {
        console.error("載入打擊音效錯誤:", error);
        keysoundBuffer = null;
        isKeysoundReady = false;
        // 打擊音效載入失敗不影響主流程，遊戲仍可繼續，只是無打擊音
    } finally {
        isKeysoundLoading = false;
        updateLoadingStatus(); // Keysound 載入狀態也影響整體載入狀態顯示
    }
}

async function loadSongBackgroundImage(url) {
    if (!url) {
        console.warn("歌曲無背景圖路徑，使用預設背景。");
        songBgImage = null;
        isSongBgReady = false;
        isSongBgLoading = false;
        updateLoadingStatus(); // 更新狀態
        return;
    }
    // 創建一個臨時 Image 元素來解析 URL 並比較 src
    const tempImg = new Image();
    tempImg.src = url;
    const parsedSrc = tempImg.src; // 使用解析後的 src 進行比較和存儲

    // 如果已經載入過同一個圖，且已準備好，則無需重複載入
    if (songBgImage && songBgImage.src === parsedSrc && isSongBgReady) {
         console.log("歌曲背景圖似乎已載入，跳過重複載入:", url);
         // 即使已載入，也確保 gameInfoIllustration 預載了
         preloadGameInfoIllustration(url); // 確保遊戲內小圖也預載
         return;
    }

    isSongBgLoading = true;
    isSongBgReady = false;
    songBgImage = null; // 清空舊圖片
    console.log(`載入歌曲背景圖: ${url}...`);
    updateLoadingStatus(); // 更新狀態

    try {
        const img = new Image();
        // 預載遊戲內小曲繪 (使用同一個 URL)
        preloadGameInfoIllustration(url);

        await new Promise((resolve, reject) => {
            img.onload = () => {
                songBgImage = img;
                isSongBgReady = true;
                console.log("歌曲背景圖載入完成！");
                resolve();
            };
            img.onerror = (err) => {
                console.error(`載入歌曲背景圖錯誤 (${url}):`, err);
                songBgImage = null;
                isSongBgReady = false;
                reject(err); // 即使載入失敗也 reject，讓 Promise.all 知道
            };
            img.src = url; // 開始載入 (使用原始 src)
        });
    } catch (error) {
        // 錯誤已在 onerror 中處理並打印，這裡捕獲是為了 Promise.all
        console.log("捕獲到背景圖載入錯誤 Promise:", error);
    } finally {
        isSongBgLoading = false;
        updateLoadingStatus(); // 更新狀態
        // 背景圖載入狀態不影響主流程，不在此檢查是否觸發 Intro
    }
}


function updateLoadingStatus() {
    // 可以在這裡更新一個載入進度條或文字，如果需要的話
    // 目前只是打印狀態
    if (gameState === 'LOADING') {
        console.log(`載入狀態: SongBG ${isSongBgLoading?'中':(isSongBgReady?'完成':'失敗/未載入')}, 音訊 ${isAudioLoading ? '中' : (isAudioReady ? '完成' : '失敗/未載載')}, 譜面 ${isChartLoading ? '中' : (isChartReady ? '完成' : '失敗/未載入')}, Keysound ${isKeysoundLoading ? '中' : (isKeysoundReady ? '完成' : '失敗/未載入')}`);
        // 例如: if (loadingTextElement) { loadingTextElement.textContent = `Loading... Audio: ${isAudioReady}, Chart: ${isChartReady}, BG: ${isSongBgReady}`; }
    }
}

function checkAndTriggerIntro() {
     // 只有在 LOADING 狀態下才檢查和觸發 Intro
    if (gameState === 'LOADING') {
        // 音訊和譜面是開始遊戲的必要資源
        if (isAudioReady && isChartReady) {
            console.log("音訊和譜面均已就緒，觸發 Intro...");
            startIntro();
        } else {
             // 打印出當前狀態，幫助調試哪些資源還沒好
            console.log("等待主要資源載入中...", {isAudioReady, isChartReady, isSongBgReady, isKeysoundReady});
        }
    } else {
         console.log(`不在 LOADING 狀態 (${gameState})，不檢查觸發 Intro。`);
    }
}

// =============================================================================
// Intro 畫面處理
// =============================================================================
function showIntroScreen() {
    if (!selectedSongData) {
        console.error("無法顯示 Intro，未選歌！");
        showScreen('SELECTING'); // 回到選曲畫面
        return;
    }

    // 確保 Intro 畫面顯示正確的歌曲信息
    introIllustration.src = selectedSongData.illustrationPath || 'placeholder.png';
    introIllustration.onerror = () => {
         console.warn(`Intro 插圖載入失敗: ${introIllustration.src}. 使用預設圖。`);
         introIllustration.src = 'placeholder.png'; // 載入失敗時使用預設圖
    };
    introTitle.textContent = selectedSongData.title || '未知歌曲';
    introArtist.textContent = selectedSongData.artist || '未知作曲家';

    // 切換到 Intro 畫面
    showScreen('INTRO');
    console.log("Intro 顯示，開始 Intro 定時器...");

    // Intro 畫面持續一段時間，然後淡出，再開始遊戲
    // 設置 Intro 顯示時間 (3秒)
    setTimeout(() => {
        if (gameState === 'INTRO') { // 確保狀態未變
            console.log("Intro 顯示時間到，開始淡出 Intro 畫面...");
            introScreen.classList.remove('visible'); // 觸發淡出

            // 等待淡出動畫完成後，設置遊戲開始延遲
            setTimeout(() => {
                if (gameState === 'INTRO') { // 確保狀態在淡出期間未變
                    console.log(`Intro 淡出完成，等待 ${INTRO_TO_GAME_DELAY_SECONDS} 秒後開始遊戲...`);
                    // 設置遊戲開始前的延遲
                    gameStartDelayTimeoutId = setTimeout(() => {
                        if (gameState === 'INTRO') { // 最終檢查狀態，確保在等待期間未返回選單等
                            console.log("遊戲開始延遲定時器觸發，開始播放...");
                            gameStartDelayTimeoutId = null; // 清除定時器 ID
                            playAudio(); // 播放音訊並啟動遊戲循環
                        } else {
                            console.log("遊戲開始延遲定時器觸發，但狀態已變，不播放音樂。");
                             gameStartDelayTimeoutId = null;
                        }
                    }, INTRO_TO_GAME_DELAY_SECONDS * 1000); // 將秒轉換為毫秒
                } else {
                     console.log("Intro 淡出完成定時器觸發，但狀態已變。");
                }
            }, 500); // 等待 CSS 淡出動畫完成的時間 (假設 500ms)
        } else {
            console.log("Intro 顯示定時器觸發，但狀態已變，不執行後續操作。");
        }
    }, 3000); // Intro 畫面顯示 3 秒
}
// 別名方便使用
const startIntro = showIntroScreen;


// =============================================================================
// 音訊播放與遊戲流程控制
// =============================================================================
function playKeysound() {
    if (isKeysoundReady && keysoundBuffer && audioContext && audioContext.state === 'running') {
        try {
            const source = audioContext.createBufferSource();
            source.buffer = keysoundBuffer;
            // 使用 GainNode 控制音量
            const gainNode = audioContext.createGain();
            gainNode.gain.value = KEYSOUND_VOLUME;
            source.connect(gainNode);
            gainNode.connect(audioContext.destination);
            source.start(0); // 立即播放
        } catch (error) {
            console.error("播放打擊音效失敗:", error);
            // 播放失敗可能是資源問題或 AC 狀態問題，但在遊戲中不應該頻繁彈窗
        }
    } else {
        // console.warn("打擊音效未準備好或 AC 狀態異常，無法播放。");
    }
}

function playAudio() {
    if (isPlaying || !audioContext || !audioBuffer || !chartData) {
        console.warn("無法播放歌曲，狀態或資源異常。", {isPlaying, audioContextExists: !!audioContext, audioBufferExists: !!audioBuffer, chartDataExists: !!chartData });
        // 如果無法播放，回到選曲畫面 (雖然 initializeAudioContextAndLoad 中也可能處理)
        if (gameState !== 'SELECTING') showScreen('SELECTING');
        return;
    }

    // 確保在播放前切換到遊戲畫面
    showScreen('GAME');

    // 停止可能存在的舊音源
    if (audioSource) {
        try { audioSource.stop(); } catch(e) { console.warn("停止舊音源時出錯(可能已停止):", e); }
        audioSource.disconnect();
        audioSource = null;
    }

    // 創建新的音源
    audioSource = audioContext.createBufferSource();
    audioSource.buffer = audioBuffer;
    audioSource.connect(audioContext.destination);

    // 計算預計開始播放的 AudioContext 時間
    const scheduledStartTime = audioContext.currentTime + START_DELAY_SECONDS;
    audioStartTime = scheduledStartTime; // 記錄實際開始時間
    isPlaying = true;
     // 遊戲內時間從 -START_DELAY_SECONDS 開始計時
    rawElapsedTime = -START_DELAY_SECONDS;
    currentSongTime = 0; // 歌曲時間從 0 開始計時 (用於判定等遊戲邏輯)

    console.log(`音樂預計開始於 AC 時間: ${audioStartTime.toFixed(3)}`);

    // 在開始播放前初始化遊戲狀態變數 (分數、連擊、音符狀態等)
    initializeGameState();

    // 設定音樂播放結束時的事件
    audioSource.onended = () => {
        console.log("音樂播放結束事件觸發。");
        const wasPlaying = isPlaying; // 判斷是否是正常播放結束
        isPlaying = false; // 標記為不播放
        audioSource = null; // 清空音源引用

        // 只有在音樂正常播放結束且狀態為遊戲中時，才顯示結算畫面
        // (避免在返回選單等情況下觸發結算)
        if (wasPlaying && (gameState === 'PLAYING' || gameState === 'GAME')) {
            console.log("音樂自然結束，顯示結算畫面。");
            showResultScreen();
        } else {
            console.log(`音樂結束，但狀態為 ${gameState} 或非自然停止 (wasPlaying: ${wasPlaying})，不顯示結算。`);
        }
    };

    // 啟動音源，設置延遲播放
    audioSource.start(scheduledStartTime, 0);

    // 如果遊戲迴圈未運行，啟動它
    if (!gameLoopRunning) {
        console.log("遊戲迴圈啟動...");
        gameLoopRunning = true;
        requestAnimationFrame(gameLoop);
    } else {
         // 這應該不會發生，除非 playAudio 被重複呼叫且 gameLoopRunning 沒有正確標記為 false
        console.warn("playAudio 被調用，但 gameLoopRunning 已經是 true？");
    }
     // 狀態細化：從 GAME 切換到 PLAYING
    gameState = 'PLAYING';
    console.log("遊戲狀態切換到: PLAYING");
}


function startGame(songData) {
    if (!songData || !songData.audioPath || !songData.chartPath) {
        console.error("無效歌曲數據！無法開始遊戲。");
        alert("選擇的歌曲資料不完整！");
        showScreen('SELECTING'); // 返回選曲畫面
        return;
    }
    // 保存選中的歌曲數據
    selectedSongData = songData;
    console.log(`選中歌曲: ${selectedSongData.title}`);

    // 重置資源狀態標誌 (不需要重置遊戲內曲繪和背景圖的狀態，它們會在載入新圖時更新)
    isAudioReady = false;
    isChartReady = false;
    // 清空舊的緩存資源
    audioBuffer = null;
    chartData = null;
    loadedNotes = [];
    totalNotesInChart = 0;
    baseScorePerPerfect = 0;

    // 重置遊戲狀態變數 (分數、連擊、音符狀態等)
    initializeGameState(); // 现在这个函数不重置图片状态

    // 切換到載入畫面
    showScreen('LOADING');

    // 初始化 AudioContext 並開始載入資源
    initializeAudioContextAndLoad();
}

function initializeAudioContextAndLoad() {
     // 確保 AudioContext 已被點擊 Splash Screen 時初始化
    if (!audioContext) {
        console.error("AudioContext 未初始化！無法載入資源。請確保在 handleSplashScreenClick 中初始化。");
        alert("音訊系統尚未準備好，請重試 (可能需要重新整理並點擊畫面)。");
        showScreen('SELECTING'); // 返回選曲畫面
        return;
    }

    const loadResources = async () => {
        console.log("AC 狀態:", audioContext.state, "準備載入資源...");
        updateLoadingStatus(); // 更新載入狀態顯示

        const loadPromises = [];

        // 載入歌曲背景圖 (非必要，但可以等待)
        if (selectedSongData?.illustrationPath) {
            loadPromises.push(loadSongBackgroundImage(selectedSongData.illustrationPath)); // loadSongBackgroundImage 也會預載 gameInfoIllustration
        } else {
            console.warn("未提供歌曲背景圖路徑。");
            isSongBgReady = false;
            isSongBgLoading = false;
            songBgImage = null;
             // 如果沒有背景圖，也需要清空遊戲內曲繪的狀態
             gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;
        }

        // 載入打擊音效 (非必要，但建議等待)
        if (!isKeysoundReady && !isKeysoundLoading) { // 只在未載入或載入中時才添加
             loadPromises.push(loadKeysound());
        } else {
             console.log("打擊音效已在載入中或已完成，跳過。");
        }


        // 載入歌曲音訊 (必要)
        if (selectedSongData.audioPath) {
            // loadAudio 內部已經包含 Promise 和錯誤處理，只需呼叫它
             loadPromises.push(loadAudio(selectedSongData.audioPath));
        } else {
            console.error("錯誤：歌曲缺少音訊檔案路徑！");
            alert("錯誤：選擇的歌曲缺少音訊檔案！");
             showScreen('SELECTING'); // 返回選曲畫面
            return; // 中斷載入流程
        }

        // 載入歌曲譜面 (必要)
        if (selectedSongData.chartPath) {
            // loadChart 內部已經包含 Promise 和錯誤處理，只需呼叫它
            loadPromises.push(loadChart(selectedSongData.chartPath));
        } else {
            console.error("錯誤：歌曲缺少譜面檔案路徑！");
            alert("錯誤：選擇的歌曲缺少譜面檔案！");
             showScreen('SELECTING'); // 返回選曲畫面
            return; // 中斷載入流程
        }

        try {
            // 等待所有必要的載入 Promise 完成 (音訊和譜面)
            // 注意：Promise.all 會在任何一個 Promise reject 時立即 reject
            // 所以 loadAudio 和 loadChart 內部錯誤處理應該確保它們不會直接 reject，或者 Promise.all 外層要捕獲
             await Promise.all(loadPromises.filter(Boolean)); // 過濾掉可能為 null 的 Promise
            console.log("所有主要資源載入 Promise 完成。");
        } catch (error) {
            // 如果 loadAudio 或 loadChart 內部拋出錯誤並導致 Promise reject，這裡會捕獲
            console.error("資源載入過程中出現未捕獲的錯誤 (Promise.all):", error);
            // 錯誤處理應該在 loadAudio/loadChart 內部完成，並已經切換到 SELECTING
            // 這裡只是備用捕獲
        } finally {
            updateLoadingStatus(); // 最終更新載入狀態
             // 不論 Promise.all 結果如何，只要 isAudioReady 和 isChartReady 均為 true，就可以觸發 Intro
            checkAndTriggerIntro();
        }
    };

    // 根據 AudioContext 的狀態來決定何時開始載入
    if (audioContext.state === 'suspended') {
        console.warn("AC 處於 suspended 狀態，嘗試恢復...");
        audioContext.resume().then(() => {
            console.log("AC 已成功恢復！");
            loadResources(); // 恢復成功後開始載入資源
        }).catch(err => {
            console.error("恢復 AC 失敗:", err);
            alert("無法啟用音訊。請嘗試與頁面互動（點擊/按鍵）或檢查瀏覽器設定。");
            showScreen('SELECTING'); // 恢復失敗，返回選曲畫面
        });
    } else if (audioContext.state === 'running') {
        console.log("AC 已在運行中，直接載入資源。");
        loadResources(); // 直接開始載入資源
    } else {
        console.error("AC 處於意外狀態:", audioContext.state);
        alert(`音訊系統狀態異常 (${audioContext.state})，無法載入歌曲。`);
        showScreen('SELECTING'); // 狀態異常，返回選曲畫面
    }
}


function showResultScreen() {
    // 停止遊戲循環和音訊播放
    gameLoopRunning = false;
    isPlaying = false;
    if (audioSource) {
        try { audioSource.stop(); } catch(e) {console.warn("停止音源時出錯(可能已停止):", e);}
        audioSource.disconnect();
        audioSource = null;
    }

    // 確保總音符數不為 0，避免除以零
    let finalScore = score;
     if (totalNotesInChart > 0) {
        // 檢查是否為 All Perfect
        if (judgmentCounts.perfect === totalNotesInChart && judgmentCounts.great === 0 && judgmentCounts.good === 0 && judgmentCounts.miss === 0) {
            console.log("檢測到 All Perfect! 強制設定分數為 1,000,000。");
            finalScore = MAX_SCORE;
        }
     } else {
         console.warn("總音符數為 0，無法計算最終分數。");
         finalScore = 0; // 或其他合適的默認值
     }


    // 獲取結算畫面元素
    const resultSongTitle = document.getElementById('result-title');
    const resultArtist = document.getElementById('result-artist');
    const resultIllustrationImg = document.getElementById('result-illustration');
    const resultScore = document.getElementById('result-score');
    const resultMaxCombo = document.getElementById('result-max-combo');
    const resultPerfect = document.getElementById('result-perfect');
    const resultGreat = document.getElementById('result-great');
    const resultGood = document.getElementById('result-good');
    const resultMiss = document.getElementById('result-miss');
    let backButton = document.getElementById('back-to-select-button'); // 使用 let 因為可能會替換

    // 基本元素檢查
    if (!resultScreen || !resultSongTitle || !resultArtist || !resultIllustrationImg || !resultScore || !resultMaxCombo || !resultPerfect || !resultGreat || !resultGood || !resultMiss || !backButton) {
        console.error("找不到結算畫面必要的 HTML 元素！無法顯示結算。");
        showScreen('SELECTING'); // 返回選曲畫面
        return;
    }

    // 填充結算畫面內容 (使用 selectedSongData，因此它不能在 initializeGameState 中被清空)
    resultSongTitle.textContent = selectedSongData ? selectedSongData.title : '未知';
    resultArtist.textContent = selectedSongData ? selectedSongData.artist : '未知';
    resultIllustrationImg.src = selectedSongData ? selectedSongData.illustrationPath : 'placeholder.png';
    resultIllustrationImg.onerror = () => {
        console.warn(`結算畫面插圖載入失敗: ${resultIllustrationImg.src}. 使用預設圖。`);
        resultIllustrationImg.src = 'placeholder.png'; // 載入失敗時使用預設圖
    };

    // 格式化分數 (確保是整數)
    resultScore.textContent = Math.round(finalScore).toString().padStart(7, '0');
    resultMaxCombo.textContent = maxCombo;
    resultPerfect.textContent = judgmentCounts.perfect;
    resultGreat.textContent = judgmentCounts.great;
    resultGood.textContent = judgmentCounts.good;
    resultMiss.textContent = judgmentCounts.miss;

    // 為返回按鈕添加監聽器。一種更健壯的方法是檢查監聽器是否已存在，或者只在初始化時綁定一次
    // 這裡沿用替換節點的方式，但更推薦直接綁定一次並依賴 showScreen 的狀態判斷
    const newBackButton = backButton.cloneNode(true); // 克隆節點，移除所有事件監聽器
     if (backButton.parentNode) {
        backButton.parentNode.replaceChild(newBackButton, backButton); // 替換舊節點
        backButton = newBackButton; // 更新 backButton 引用
     } else {
          console.warn("無法替換返回按鈕，父節點未找到。舊按鈕監聽器可能殘留。");
     }
    backButton.addEventListener('click', handleBackToSelectClick); // 添加新的監聽器

    // 切換到結算畫面
    showScreen('RESULT');
    console.log("顯示結算畫面");

    // selectedSongData 不在此處清空，會在返回 select 時由 showScreen 內部清理
}

// =============================================================================
// 繪圖函式 (Drawing Functions)
// =============================================================================
function drawPerspectiveStaticElements() {
    if (!ctx) return;
    const originalLineWidth = ctx.lineWidth;

    // 繪製軌道分隔線
    ctx.strokeStyle = COLOR_LANE_SEPARATOR;
    ctx.lineWidth = 1;
    for (let i = 1; i < LANE_COUNT; i++) {
        const topX = getInterpolatedX(i, 0);
        const bottomX = getInterpolatedX(i, canvas.height);
        ctx.beginPath();
        ctx.moveTo(topX, 0);
        ctx.lineTo(bottomX, canvas.height);
        ctx.stroke();
    }

    // 繪製左右邊框線
    ctx.strokeStyle = COLOR_LINES;
    ctx.lineWidth = 6; // 比分隔線粗一點
    ctx.beginPath();
    ctx.moveTo(getInterpolatedX(0, 0), 0); // 左上角
    ctx.lineTo(getInterpolatedX(0, canvas.height), canvas.height); // 左下角
    ctx.stroke();

    ctx.beginPath();
    ctx.moveTo(getInterpolatedX(LANE_COUNT, 0), 0); // 右上角
    ctx.lineTo(getInterpolatedX(LANE_COUNT, canvas.height), canvas.height); // 右下角
    ctx.stroke();

    // 繪製判定線 (基本線) - 脈衝效果會在上面疊加繪製
    ctx.strokeStyle = COLOR_JUDGMENT_LINE;
    ctx.lineWidth = 3;
    const judgmentLeftX = getInterpolatedX(0, JUDGMENT_LINE_Y);
    const judgmentRightX = getInterpolatedX(LANE_COUNT, JUDGMENT_LINE_Y);
    ctx.beginPath();
    ctx.moveTo(judgmentLeftX, JUDGMENT_LINE_Y);
    ctx.lineTo(judgmentRightX, JUDGMENT_LINE_Y);
    ctx.stroke();

    ctx.lineWidth = originalLineWidth; // 恢復線寬
}

function drawNotes() {
    if (!ctx || !loadedNotes) return;

    ctx.fillStyle = COLOR_NOTE;

    loadedNotes.forEach(note => {
        // 只繪製尚未判定且活躍 (已進入屏幕並移動中) 的音符
        // **修改點：添加 note.isActive 的檢查**
        if (!note.judged && note.isActive) { // <--- 添加 isActive 檢查

            const topY = note.y; // 音符頂部的 Y 座標 (在 gameLoop 中計算)

            // 計算音符當前 Y 座標處的寬度
            const topLeftX = getInterpolatedX(note.column, topY);
            const topRightX = getInterpolatedX(note.column + 1, topY);
            const widthAtTop = topRightX - topLeftX;

            // 獲取音符在判定線處的預計寬度 (用於縮放音符高度)
            const judgmentLeftX = getInterpolatedX(note.column, JUDGMENT_LINE_Y);
            const judgmentRightX = getInterpolatedX(note.column + 1, JUDGMENT_LINE_Y);
            const widthAtJudgment = judgmentRightX - judgmentLeftX;

            // 根據透視效果，計算音符當前 Y 座標處的視覺高度縮放比例
            // 如果判定線寬度為0 (避免除以零)，縮放比例設為1
            const heightScale = (widthAtJudgment > 0) ? (widthAtTop / widthAtJudgment) : 1;
             // 設置一個最小縮放比例，避免音符在頂部變得太小
            const minHeightScale = 0.1; // 音符在屏幕頂部時的最小高度比例
            const clampedHeightScale = Math.max(minHeightScale, heightScale);

            // 計算音符的當前視覺高度
            const currentVisualHeight = NOTE_HEIGHT * clampedHeightScale;
            const bottomY = topY + currentVisualHeight; // 音符底部的 Y 座標

            // 僅在音符的任何部分可能在畫布範圍內時繪製 (這個檢查可以保留，作為輔助裁剪)
            // 考慮到音符可能滑出屏幕下方，檢查 bottomY 是否在 canvas 上方 + buffer
            // 和 topY 是否在 canvas 下方 - buffer
            const visibilityBuffer = currentVisualHeight; // 給予音符高度的緩衝
            if (bottomY > -visibilityBuffer && topY < canvas.height + visibilityBuffer) {

                const bottomLeftX = getInterpolatedX(note.column, bottomY);
                const bottomRightX = getInterpolatedX(note.column + 1, bottomY);

                // 使用 beginPath, moveTo, lineTo, closePath, fill 繪製一個梯形/矩形
                ctx.beginPath();
                ctx.moveTo(topLeftX, topY);
                ctx.lineTo(topRightX, topY);
                ctx.lineTo(bottomRightX, bottomY);
                ctx.lineTo(bottomLeftX, bottomY);
                ctx.closePath();
                ctx.fill();
            }
        }
         // Judged notes or inactive notes will not be drawn here.
    });
}


function drawJudgmentFeedback() {
    if (!ctx) return;

    // 檢查是否有最近的判定需要顯示，且時間在顯示時長內
    if (lastJudgment.text && currentSongTime >= 0 && currentSongTime < lastJudgment.time + JUDGMENT_DISPLAY_DURATION) {
        const timeSinceJudgment = currentSongTime - lastJudgment.time;
        // 根據時間計算透明度 (淡出效果)
        const alpha = 1.0 - (timeSinceJudgment / JUDGMENT_DISPLAY_DURATION);

        ctx.font = `bold 56px ${FONT_FAMILY_CANVAS}`; // 判定文字字體大小
        ctx.textAlign = 'center'; // 文字居中對齊

        // 根據判定結果選擇顏色
        let judgmentColor = 'rgba(255, 255, 255, '; // 默認白色
        if (lastJudgment.text === 'Perfect') judgmentColor = COLOR_PERFECT_PARTICLE;
        else if (lastJudgment.text === 'Great') judgmentColor = COLOR_GREAT_PARTICLE;
        else if (lastJudgment.text === 'Good') judgmentColor = COLOR_GOOD_PARTICLE;
        else if (lastJudgment.text === 'Miss') judgmentColor = 'rgba(255, 0, 0, '; // Miss 使用紅色

        // 設置填充顏色，包含計算出的透明度
        ctx.fillStyle = judgmentColor + Math.max(0, alpha) + ')'; // 確保 alpha 不小於 0

        // 繪製判定文字
        const centerX = canvas.width / 2;
        const feedbackY = JUDGMENT_LINE_Y - 80; // 在判定線上方的特定位置顯示
        ctx.fillText(lastJudgment.text, centerX, feedbackY);
    }
}


function drawScoreAndCombo() {
    if (!ctx) return;

    // 繪製分數
    ctx.fillStyle = '#FFFFFF'; // 分數顏色
    ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`; // 分數字體大小
    ctx.textAlign = 'right'; // 右對齊
    // 將分數四捨五入並格式化為7位數字，不足前面補0
    ctx.fillText(Math.round(score).toString().padStart(7, '0'), canvas.width - 20, 40);

    // 繪製 Combo (只有 Combo > 0 時顯示)
    if (combo > 0) {
        ctx.font = `bold 64px ${FONT_FAMILY_CANVAS}`; // Combo 字體大小 (更大)
        ctx.textAlign = 'center'; // 居中對齊
        const comboX = canvas.width / 2;
        const comboY = JUDGMENT_LINE_Y - 200; // 在判定線更高的位置顯示
        ctx.fillStyle = '#FFFF00'; // Combo 顏色 (黃色)
        ctx.fillText(combo, comboX, comboY);

        // 繪製 "Combos" 文字 (只有 Combo > 1 時顯示)
        if (combo > 1) {
            ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`; // "Combos" 字體大小
            ctx.fillStyle = '#FFFFFF'; // "Combos" 顏色
            ctx.fillText('Combos', comboX, comboY + 45); // 在 Combo 數字下方顯示
        }
    }

    // 繪製 Max Combo
    ctx.font = `bold 20px ${FONT_FAMILY_CANVAS}`; // Max Combo 字體大小
    ctx.fillStyle = '#CCCCCC'; // Max Combo 顏色
    ctx.textAlign = 'right'; // 右對齊
    ctx.fillText(`Max Combo: ${maxCombo}`, canvas.width - 20, 70); // 在分數下方顯示
}


function preloadGameInfoIllustration(src) {
    if (!src) {
        // console.warn("遊戲內曲繪路徑為空。");
        // 如果沒有src，清空相關狀態，避免繪製舊圖
        gameInfoIllustration = null;
        gameInfoIllustrationSrc = '';
        gameInfoIllustrationLoaded = false;
        return;
    }
    // 創建一個臨時 Image 元素來解析 URL 並比較 src
    const tempImg = new Image();
    tempImg.src = src;
    const parsedSrc = tempImg.src; // 使用解析後的 src 進行比較和存儲

    // 如果當前顯示的圖就是這個，且已經載入完成，則無需重複載入
    if (gameInfoIllustrationSrc === parsedSrc && gameInfoIllustrationLoaded && gameInfoIllustration && gameInfoIllustration.complete && gameInfoIllustration.naturalWidth > 0) {
        // console.log("遊戲內曲繪已預載且匹配當前src:", parsedSrc);
        return;
    }

     // 如果 src 改變了，或者還沒載入
    if (gameInfoIllustrationSrc !== parsedSrc) {
        console.log("準備預載新的遊戲內曲繪:", src);
        gameInfoIllustrationSrc = parsedSrc; // 更新目標 src (使用解析後的完整 src)
        gameInfoIllustrationLoaded = false; // 標記為未載入
        gameInfoIllustration = new Image(); // 創建新的 Image 物件

        gameInfoIllustration.onload = () => {
            console.log("遊戲內曲繪載入完成:", gameInfoIllustration.src);
             // 檢查載入完成的圖是否仍然是當前需要的圖，避免異步載入導致的錯誤圖片顯示
            if (gameInfoIllustrationSrc === gameInfoIllustration.src) {
                 gameInfoIllustrationLoaded = true;
            } else {
                 console.log("遊戲內曲繪載入完成，但目標 src 已改變。忽略此次載入結果。");
                 // 這裡不清空 gameInfoIllustration 和 gameInfoIllustrationSrc，讓下一次檢查能識別出目標 src 已經變了
            }
        };
        gameInfoIllustration.onerror = () => {
            console.warn("遊戲內曲繪載入失敗:", src);
             // 只有當前目標 src 載入失敗時才清空，避免清除其他已載入成功的圖
             if (gameInfoIllustrationSrc === parsedSrc) {
                gameInfoIllustration = null;
                gameInfoIllustrationSrc = ''; // 清空失敗的 src
             }
            gameInfoIllustrationLoaded = false;
        };
        gameInfoIllustration.src = src; // 開始載入 (使用原始 src)
    } else {
         // src 相同，但 loaded 為 false，說明正在載入中或載入失敗但還沒清空 src，等待其 onload/onerror 即可
         // console.log("遊戲內曲繪正在載入中或載入失敗狀態:", parsedSrc);
    }
}


function drawGameInfo() {
    if (!ctx || !selectedSongData) return;

    const margin = 20;
    const imageSize = 50;
    const textSpacing = 8;
    const titleFontSize = 20;
    const artistFontSize = 14;

    const currentIllustrationPath = selectedSongData.illustrationPath || '';
    // 創建一個臨時 Image 元素來解析 URL
    const tempImg = new Image();
    tempImg.src = currentIllustrationPath;
    const currentIllustrationSrcParsed = tempImg.src; // 用於比較

    // 確保圖片被載入 (這個邏輯應該在 loadSongBackgroundImage 或 startGame 中觸發，這裡主要用於繪製)
    // if (currentIllustrationPath && !gameInfoIllustrationLoaded && !gameInfoIllustrationSrc === currentIllustrationSrcParsed) {
    //     preloadGameInfoIllustration(currentIllustrationPath);
    // }
     // 簡化: drawGameBackground 已經觸發 loadSongBackgroundImage，而 loadSongBackgroundImage 會觸發 preloadGameInfoIllustration
     // 所以這裡只需要檢查狀態並繪製

    // 繪製遊戲內小曲繪
    // 只有在圖片存在、載入完成且是當前歌曲的圖片時才繪製
    if (gameInfoIllustration && gameInfoIllustrationLoaded && gameInfoIllustration.src === currentIllustrationSrcParsed) {
        try {
            ctx.globalAlpha = 0.8; // 設置透明度
            ctx.drawImage(gameInfoIllustration, margin, margin, imageSize, imageSize);
            ctx.globalAlpha = 1.0; // 恢復透明度
        } catch (e) {
            console.error("繪製遊戲內曲繪時出錯:", e, gameInfoIllustration);
            // 繪製失敗，可能是圖片數據問題，標記為未載入以便下次重試或使用預設
             gameInfoIllustrationLoaded = false;
             gameInfoIllustration = null;
        }
    } else {
        // console.log("遊戲內曲繪未準備好繪製:", { gameInfoIllustration: !!gameInfoIllustration, gameInfoIllustrationLoaded, gameInfoIllustrationSrc, currentIllustrationSrcParsed }); // 調試用
    }


    // 繪製歌曲標題和作曲家
    ctx.fillStyle = 'rgba(255, 255, 255, 0.9)'; // 文字顏色
    ctx.textAlign = 'left';
    ctx.textBaseline = 'top'; // 從頂部對齊文字，方便計算位置
    ctx.font = `bold ${titleFontSize}px ${FONT_FAMILY_CANVAS}`;
    ctx.fillText(selectedSongData.title || '未知', margin + imageSize + textSpacing, margin + 5); // 在圖片右側稍靠下

    ctx.font = `${artistFontSize}px ${FONT_FAMILY_CANVAS}`;
    ctx.fillStyle = 'rgba(204, 204, 204, 0.9)'; // 作曲家文字顏色稍暗
    ctx.fillText(selectedSongData.artist || '未知', margin + imageSize + textSpacing, margin + titleFontSize + 8); // 在標題下方

    ctx.textBaseline = 'alphabetic'; // 恢復文字基線為默認
}


// =============================================================================
// 特效更新與繪製函數
// =============================================================================
function updateAndDrawHitEffects(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的粒子效果
    activeHitEffects = activeHitEffects.filter(effect => {
        effect.particles = effect.particles.filter(particle => currentTime - particle.startTime < particle.lifetime);
        return effect.particles.length > 0; // 如果效果中沒有粒子了，就移除這個效果
    });

    // 繪製每個粒子
    activeHitEffects.forEach(effect => {
        effect.particles.forEach(particle => {
            const elapsedTime = currentTime - particle.startTime;
            const lifetimeRatio = elapsedTime / particle.lifetime;
            const easedAlphaProgress = easeOutCubic(lifetimeRatio);

            // 更新粒子位置 (基於簡易的線性運動)
            particle.x += particle.vx * (1/60); // 假設 60 FPS
            particle.y += particle.vy * (1/60); // 假設 60 FPS
             // 更新粒子旋轉
            particle.rotation += particle.angularVelocity * (1/60); // 假設 60 FPS

            // 更新粒子透明度 (淡出)
            particle.alpha = Math.max(0, 1.0 - easedAlphaProgress);

            // 繪製粒子 (繪製為三角形)
            ctx.save(); // 保存當前 Canvas 狀態
            ctx.fillStyle = particle.color + particle.alpha + ')'; // 設置填充顏色和透明度
            ctx.globalAlpha = particle.alpha; // 單獨設置 globalAlpha 也可以
            ctx.translate(particle.x, particle.y); // 將原點移到粒子中心
            ctx.rotate(particle.rotation); // 旋轉 Canvas
            const side = particle.size;
            const height = side * Math.sqrt(3) / 2;
            ctx.beginPath();
            ctx.moveTo(0, -height / 2); // 頂點
            ctx.lineTo(-side / 2, height / 2); // 左下角
            ctx.lineTo(side / 2, height / 2); // 右下角
            ctx.closePath();
            ctx.fill();
            ctx.restore(); // 恢復 Canvas 狀態 (取消 translate 和 rotate)
        });
    });
     ctx.globalAlpha = 1.0; // 確保恢復全局透明度
}

function updateAndDrawLaneFlashes(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的軌道閃爍效果
    activeLaneFlashes = activeLaneFlashes.filter(flash => currentTime - flash.startTime < flash.duration);

    // 繪製每個軌道閃爍效果
    activeLaneFlashes.forEach(flash => {
        const elapsedTime = currentTime - flash.startTime;
        const progress = elapsedTime / flash.duration;
         // 使用緩和函數控制透明度變化 (例如，緩慢淡出)
        const alpha = Math.max(0, 1.0 - easeOutCubic(progress)); // 從 1 漸變到 0

        const laneIndex = flash.laneIndex;

        // 計算軌道在判定線和頂部的四個點的 X 座標 (用於繪製與透視對齊的區域)
        const bottomX1 = getInterpolatedX(laneIndex, JUDGMENT_LINE_Y);
        const bottomX2 = getInterpolatedX(laneIndex + 1, JUDGMENT_LINE_Y);
        const topX1 = getInterpolatedX(laneIndex, 0);
        const topX2 = getInterpolatedX(laneIndex + 1, 0);

        // 創建從判定線到頂部的線性漸變
        const gradient = ctx.createLinearGradient(0, JUDGMENT_LINE_Y, 0, 0); // 垂直方向漸變
        gradient.addColorStop(0, COLOR_LANE_FLASH + alpha + ')'); // 判定線處使用當前透明度
        gradient.addColorStop(1, COLOR_LANE_FLASH + '0)'); // 頂部完全透明

        ctx.fillStyle = gradient; // 設置填充樣式為漸變

        // 繪製表示軌道的梯形區域
        ctx.beginPath();
        ctx.moveTo(topX1, 0);
        ctx.lineTo(topX2, 0);
        ctx.lineTo(bottomX2, JUDGMENT_LINE_Y);
        ctx.lineTo(bottomX1, JUDGMENT_LINE_Y);
        ctx.closePath();
        ctx.fill(); // 填充軌道區域
    });
}

function updateAndDrawRingEffects(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的光環效果
    activeRingEffects = activeRingEffects.filter(ring => currentTime - ring.startTime < ring.duration);

    // 繪製每個光環效果
    activeRingEffects.forEach(ring => {
        const elapsedTime = currentTime - ring.startTime;
        const progress = elapsedTime / ring.duration;
         // 使用緩和函數控制縮放和透明度變化 (例如，緩慢擴散並淡出)
        const easedProgress = easeOutCubic(progress); // 0 到 1 的緩和進度

        // 計算當前光環的大小
        const currentScale = RING_EFFECT_START_SCALE + (RING_EFFECT_END_SCALE - RING_EFFECT_START_SCALE) * easedProgress;
        // 計算當前光環的透明度 (從 1 漸變到 0)
        const currentAlpha = Math.max(0, 1.0 - easedProgress);

        // 根據起始寬度和縮放比例計算當前的寬度和高度
        // ring.startWidth 是在判定線處的軌道寬度
        const currentWidth = ring.startWidth * currentScale;
         // 高度使用起始寬度的一個比例，並應用相同的縮放
        const currentHeight = (ring.startWidth / 2.5) * currentScale; /* 使用者調整後的值: /2.5 使其更扁 */

        ctx.save(); // 保存 Canvas 狀態
        ctx.globalAlpha = currentAlpha; // 設置全局透明度
        ctx.strokeStyle = COLOR_RING_EFFECT + currentAlpha + ')'; // 設置線條顏色和透明度
        ctx.lineWidth = RING_EFFECT_LINE_WIDTH; // 設置線寬

        // 添加發光效果
        ctx.shadowColor = RING_GLOW_COLOR;
        ctx.shadowBlur = RING_GLOW_BLUR;

        // 繪製橢圓 (代表光環)。中心在判定點。
        ctx.beginPath();
        ctx.ellipse(
            ring.centerX, // 橢圓中心 X 座標 (判定點 X)
            ring.centerY, // 橢圓中心 Y 座標 (判定線 Y)
            currentWidth / 2, // X 軸半徑 (寬度的一半)
            currentHeight / 2, // Y 軸半徑 (高度的一半)
            0, // 旋轉角度 (0 表示不旋轉)
            0, // 開始角度
            2 * Math.PI // 結束角度
        );
        ctx.stroke(); // 繪製橢圓的邊框

        ctx.restore(); // 恢復 Canvas 狀態 (取消 globalAlpha, shadow 等設置)
    });
     ctx.globalAlpha = 1.0; // 確保恢復全局透明度
}


function updateAndDrawShockwaves(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的衝擊波效果
    activeShockwaves = activeShockwaves.filter(wave => currentTime - wave.startTime < wave.duration);

    // 繪製每個衝擊波效果
    activeShockwaves.forEach(wave => {
        const elapsedTime = currentTime - wave.startTime;
        const progress = elapsedTime / wave.duration;
         // 使用緩和函數控制縮放和透明度變化 (快速擴散並淡出)
        const easedProgress = easeOutCubic(progress); // 0 到 1 的緩和進度

        // 計算當前衝擊波的大小
        const currentScale = SHOCKWAVE_START_SCALE + (SHOCKWAVE_END_SCALE - SHOCKWAVE_START_SCALE) * easedProgress;
        // 計算當前衝擊波的透明度 (從 1 漸變到 0)
        const currentAlpha = Math.max(0, 1.0 - easedProgress);

        // 根據起始寬度和縮放比例計算當前的寬度和高度
        // wave.startWidth 是在判定線處的軌道寬度
        const currentWidth = wave.startWidth * currentScale;
         // 高度使用起始寬度的一個比例，並應用相同的縮放 (這裡更扁一些)
        const currentHeight = (wave.startWidth / 1.5) * currentScale;

        ctx.save(); // 保存 Canvas 狀態
        ctx.globalAlpha = currentAlpha; // 設置全局透明度
        ctx.fillStyle = wave.color + currentAlpha + ')'; // 設置填充顏色和透明度 (注意，衝擊波是填充而不是邊框)

        // 繪製填充的橢圓 (代表衝擊波)。中心在判定點。
        ctx.beginPath();
        ctx.ellipse(
            wave.centerX, // 橢圓中心 X 座標 (判定點 X)
            wave.centerY, // 橢圓中心 Y 座標 (判定線 Y)
            currentWidth / 2, // X 軸半徑
            currentHeight / 2, // Y 軸半徑
            0, // 旋轉角度
            0, // 開始角度
            2 * Math.PI // 結束角度
        );
        ctx.fill(); // 填充橢圓

        ctx.restore(); // 恢復 Canvas 狀態
    });
     ctx.globalAlpha = 1.0; // 確保恢復全局透明度
}

function updateAndDrawJudgmentLinePulses(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的判定線脈衝效果
    activeJudgmentLinePulses = activeJudgmentLinePulses.filter(pulse => currentTime - pulse.startTime < pulse.duration);

    // 判定線脈衝通常只需要繪製最新的一個，以避免疊加混亂
    const latestPulse = activeJudgmentLinePulses[activeJudgmentLinePulses.length - 1];

    if (latestPulse) {
        const elapsedTime = currentTime - latestPulse.startTime;
        const progress = elapsedTime / latestPulse.duration;

        // 使用一個脈衝效果的緩和函數 (例如 sine 函數)
        const pulseIntensity = easePulseSine(progress); // 0 到 1 再到 0 的過程

        // 計算當前的線寬和透明度 (根據脈衝強度變化)
        const currentLineWidth = 3 + (JUDGMENT_LINE_PULSE_MAX_WIDTH_MULTIPLIER - 1) * 3 * pulseIntensity;
        const currentAlpha = pulseIntensity * JUDGMENT_LINE_PULSE_MAX_ALPHA;

        ctx.save(); // 保存 Canvas 狀態
        ctx.strokeStyle = COLOR_JUDGMENT_LINE_PULSE + currentAlpha + ')'; // 設置線條顏色和透明度
        ctx.lineWidth = currentLineWidth; // 設置線寬
        ctx.globalAlpha = currentAlpha; // 設置全局透明度

        // 重新繪製判定線 (具有脈衝效果)
        const judgmentLeftX = getInterpolatedX(0, JUDGMENT_LINE_Y);
        const judgmentRightX = getInterpolatedX(LANE_COUNT, JUDGMENT_LINE_Y);
        ctx.beginPath();
        ctx.moveTo(judgmentLeftX, JUDGMENT_LINE_Y);
        ctx.lineTo(judgmentRightX, JUDGMENT_LINE_Y);
        ctx.stroke();

        ctx.restore(); // 恢復 Canvas 狀態
    }
     // 注意：即使沒有最新的脈衝效果，drawPerspectiveStaticElements 也會繪製一個基本的判定線
}

// 垂直光束特效的更新與繪製函數 (屏幕垂直光束)
function updateAndDrawLaneBeams(currentTime) {
    if (!ctx) return;

    // 過濾掉已經過期的垂直光束效果
    activeLaneBeams = activeLaneBeams.filter(beam => currentTime - beam.startTime < beam.duration);

    // 繪製每個垂直光束效果
    activeLaneBeams.forEach(beam => {
        const elapsedTime = currentTime - beam.startTime;
        const progress = elapsedTime / beam.duration;
        // 使用緩和函數控制透明度變化 (快速淡出)
        const alpha = Math.max(0, 1.0 - easeOutCubic(progress)); // 從 1 漸變到 0

        const laneIndex = beam.laneIndex;

        // 計算該軌道在判定線處的中心 X 座標
        const centerXAtJudgment = getInterpolatedX(laneIndex + 0.5, JUDGMENT_LINE_Y);
        // 獲取該軌道在判定線處的寬度
        const laneWidthAtJudgment = getInterpolatedX(laneIndex + 1, JUDGMENT_LINE_Y) - getInterpolatedX(laneIndex, JUDGMENT_LINE_Y);

        // 光束的寬度等於判定線處軌道的寬度
        const beamWidth = laneWidthAtJudgment; // <--- 使用軌道寬度

        // 計算光束矩形的左側 X 座標
        const beamLeftX = centerXAtJudgment - beamWidth / 2;

        // 光束的垂直範圍是從畫布頂部到底部判定線
        const topY = 0; // 畫布頂部 Y 座標
        const bottomY = JUDGMENT_LINE_Y; // 判定線 Y 座標

        // 創建從判定線 (底部) 到畫布頂部 (頂部) 的線性漸變
        const gradient = ctx.createLinearGradient(beamLeftX, bottomY, beamLeftX, topY); // 垂直方向漸變
        gradient.addColorStop(0, COLOR_LANE_BEAM + alpha + ')'); // 判定線處使用當前透明度
        gradient.addColorStop(0.5, COLOR_LANE_BEAM + (alpha * 0.6) + ')'); // 中間稍微透明
        gradient.addColorStop(1, COLOR_LANE_BEAM + '0)'); // 頂部完全透明


        ctx.save(); // 保存 Canvas 狀態
        ctx.globalAlpha = alpha; // 設置全局透明度 (疊加控制)

        ctx.fillStyle = gradient; // 設置填充樣式為漸變

        // 添加發光效果 (柔和光暈)
        ctx.shadowColor = COLOR_BEAM_GLOW;
        ctx.shadowBlur = BEAM_GLOW_BLUR;

        // 可選：使用 globalCompositeOperation 疊加模式來增強光感 (例如 additive 疊加)
        // ctx.globalCompositeOperation = 'lighter'; // 取消註釋此行以啟用疊加模式

        // 繪製屏幕垂直的填充矩形
        ctx.fillRect(beamLeftX, topY, beamWidth, bottomY - topY);


        ctx.restore(); // 恢復 Canvas 狀態 (取消 globalAlpha, shadow 等設置)
         // 如果使用了 globalCompositeOperation，也要在這裡恢復
         // if (ctx.globalCompositeOperation !== 'source-over') ctx.globalCompositeOperation = 'source-over'; // 恢復默認疊加模式
    });
     ctx.globalAlpha = 1.0; // 確保最終恢復全局透明度
}


// =============================================================================
// 遊戲主迴圈 (Game Loop)
// =============================================================================
function gameLoop() {
    // 檢查遊戲迴圈是否應該停止
    if (!gameLoopRunning) {
        // console.log("遊戲迴圈已標記停止，退出。"); // 避免頻繁打印
        return; // 退出迴圈
    }

    // 獲取當前時間
    // 使用 performance.now 獲取高精度時間 (秒)
    let currentTime = performance.now() / 1000; // 獲取當前時間 (秒)

    // 更新歌曲時間 (只有在播放狀態下才更新)
    if (audioContext && isPlaying && audioSource) {
        // 使用 AudioContext 的時間確保與音訊同步
        rawElapsedTime = audioContext.currentTime - audioStartTime;
         // 歌曲時間從 0 開始，且不能小於 0
        currentSongTime = Math.max(0, rawElapsedTime);
        // console.log(`rawElapsedTime: ${rawElapsedTime.toFixed(3)}, currentSongTime: ${currentSongTime.toFixed(3)}`); // 調試用
    } else {
        // 如果 isPlaying 為 true 但 AC 或 Source 丟失，說明狀態異常
        if(isPlaying) {
             console.error("遊戲狀態異常：isPlaying 為 true 但 AudioContext 或 AudioSource 丟失！");
             // 立即停止遊戲並返回選單
             gameLoopRunning = false;
             isPlaying = false;
             if (audioSource) { try{audioSource.stop();}catch(e){} audioSource.disconnect(); audioSource = null; }
             showScreen('SELECTING');
             return; // 退出迴圈
        }
         // 如果 gameLoopRunning 仍然是 true 而 isPlaying 是 false，可能是邏輯錯誤，也應該停止
         console.warn("遊戲迴圈運行中但 isPlaying 為 false。停止迴圈。", {isPlaying, gameLoopRunning});
         gameLoopRunning = false;
         // 如果狀態還是 GAME/PLAYING，可能需要觸發結算 (比如手動停止了音訊但狀態沒變)
         if (gameState === 'PLAYING' || gameState === 'GAME') {
              console.warn("遊戲迴圈檢測到 isPlaying 為 false，但狀態仍是 GAME/PLAYING，嘗試顯示結果。");
              showResultScreen(); // 這會將 gameLoopRunning 設為 false，確保下次不再運行
         }
         return; // 退出迴圈
    }


    // 檢查 Canvas context
    if (!ctx) {
        console.error("Canvas context lost!");
        gameLoopRunning = false;
        showScreen('SELECTING'); // 回到選單
        return; // 退出迴圈
    }

    // 1. 繪製背景 (包括模糊處理和變暗疊加層)
    drawGameBackground(); // 這個函數內部會調用 drawPerspectiveStaticElements 繪製靜態軌道線

    // 2. 更新音符狀態並處理超時 Miss
    if (isPlaying) { // 只有在音樂播放時才更新音符位置和判定
        loadedNotes.forEach(note => {
            // 只處理尚未判定的音符的狀態更新
            if (!note.judged) {
                // 計算音符應該出現在屏幕頂部的時間 (Y=0 的時間)
                const appearTime = note.targetTime - noteAppearTimeOffset;

                // 計算音符從 "屏幕頂部出現時間" 開始經過的時間
                const timeSinceAppear = rawElapsedTime - appearTime;

                // **修改點：根據 timeSinceAppear 來設置 isActive 和計算位置**
                // 音符只有在 timeSinceAppear >= 0 時才在屏幕上活躍並計算 Y
                if (timeSinceAppear >= 0) {
                    note.isActive = true; // 標記為活躍

                    // 計算音符從 appearTime 到 targetTime 的時間進度 (0 到 1)
                    // 如果音符滑過了 targetTime，這個 progress 會大於 1
                    const fallProgress = noteAppearTimeOffset > 0 ? (timeSinceAppear / noteAppearTimeOffset) : (rawElapsedTime >= appearTime ? 10 : -1); // 如果 offset 是 0，立即設置為較大值

                    // 使用緩和函數和線性混合計算音符的 Y 座標進度
                    // 這個 yProgress = 0 對應 appearTime 和 Y=0
                    // yProgress = 1 對應 targetTime 和 Y=JUDGMENT_LINE_Y
                    // yProgress > 1 對應時間 > targetTime 和 Y > JUDGMENT_LINE_Y (滑過)
                    const easedProgress = Math.pow(Math.max(0, fallProgress), NOTE_SPEED_EASING_POWER); // 對大於等於0的進度應用緩和
                    const yProgress = LINEAR_MIX_FACTOR * fallProgress + (1 - LINEAR_MIX_FACTOR) * easedProgress; // 線性與緩和混合

                    // 計算音符當前的 Y 座標
                    note.y = yProgress * JUDGMENT_LINE_Y;

                    // 檢查音符是否超時 (Miss) - 只有當前歌曲時間超過音符目標時間 + Miss 窗口時才判定為 Miss
                    if (currentSongTime > note.targetTime + JUDGE_WINDOW_MISS) {
                        if (!note.judged) { // 再次檢查確保未被判定 (防止重複 Miss)
                            console.log(`判定: Miss (超時) Lane ${note.column + 1} (T:${(currentSongTime - note.targetTime).toFixed(3)}s) ID: ${note.id}`);
                            note.judged = true; // 標記為已判定
                            note.judgment = 'Miss'; // 設置判定結果
                            note.isActive = false; // <--- Miss 後不再活躍 (停止繪製和更新)
                            lastJudgment = { text: 'Miss', time: currentSongTime, column: note.column }; // 更新判定文字顯示
                            combo = 0; // Break combo
                            judgmentCounts.miss++; // 增加 Miss 計數
                             // Miss 不播放打擊音效，不觸發粒子、光環、衝擊波、垂直光束特效
                             // 判定線脈衝可以考慮在 Miss 時也觸發，但這裡沒有
                        }
                    }

                    // 如果音符已經滑出屏幕很遠，也標記為不活躍，節省繪圖資源
                    // 計算一個 Y 座標的閾值，例如 canvas 高度 + 一個音符高度的緩衝
                    const offScreenThresholdY = canvas.height + NOTE_HEIGHT * 2; // 給予音符高度的緩衝
                    if (note.y > offScreenThresholdY) {
                         note.isActive = false; // <--- 滑出屏幕底部後不再活躍
                    }


                } else {
                     // 音符還沒到出現時間
                    note.isActive = false; // <--- 確保在出現時間前是不活躍的
                    note.y = 0; // <--- 確保位置在屏幕外 (或頂部)
                    // 這個階段不會產生 Miss 判定，因為還沒到 Miss 窗口
                }
            }
             // Judged notes will not be updated or drawn.
        });
    }


    // --- 繪製遊戲元素 (按順序疊加) ---

    // 特效繪製 (更新並繪製活躍的特效)
    updateAndDrawLaneFlashes(currentSongTime);      // 3. 軌道閃爍 (在軌道下方)
    updateAndDrawShockwaves(currentSongTime);       // 4. 衝擊波 (可能在判定線附近，覆蓋部分軌道)
    updateAndDrawLaneBeams(currentSongTime);        // 5. 垂直光束特效 (在軌道上方，屏幕垂直)
    drawNotes();                                    // 6. 下落的音符 (在光束上方繪製，確保音符可見)
    updateAndDrawRingEffects(currentSongTime);      // 7. 判定光環 (在判定線附近，可能覆蓋音符)
    updateAndDrawHitEffects(currentSongTime);       // 8. 粒子效果 (從判定點爆發)
    updateAndDrawJudgmentLinePulses(currentSongTime);// 9. 判定線脈衝 (在判定線上)

    // UI 繪製
    drawJudgmentFeedback();                         // 10. 判定文字 (Perfect, Great 等)
    drawScoreAndCombo();                            // 11. 分數和 Combo UI
    drawGameInfo();                                 // 12. 遊戲信息 (小曲繪、歌名等)

    // 13. 請求下一幀動畫
    if (gameLoopRunning) {
        requestAnimationFrame(gameLoop);
    } else {
        // console.log("gameLoopRunning 為 false，不請求下一幀。遊戲迴圈結束。"); // 避免頻繁打印
    }
}


// =============================================================================
// 事件監聽器設定
// =============================================================================
window.addEventListener('keydown', function(event) {
    // 防止瀏覽器默認行為，例如空格鍵滾動頁面
    // 對於遊戲鍵和 Escape 鍵，通常需要阻止默認行為
    if (KEY_MAPPINGS.includes(event.code) || event.code === 'Escape') {
        // 只有在特定狀態下才阻止 Escape 的默認行為，避免影響瀏覽器功能
         if (['PLAYING', 'GAME', 'RESULT', 'INTRO', 'LOADING'].includes(gameState) && event.code === 'Escape') {
              event.preventDefault();
         } else if (KEY_MAPPINGS.includes(event.code)) {
             event.preventDefault();
         }
    }

    const keyCode = event.code;

    // Escape 鍵處理 (返回選單)
    if (keyCode === 'Escape') {
        // 在遊戲中、結算、Intro、載入等狀態下按 Escape 返回選單
        if (['PLAYING', 'GAME', 'RESULT', 'INTRO', 'LOADING'].includes(gameState)) {
            console.log("Escape 按下，準備返回選單...");
            handleBackToSelectClick(); // 調用返回選單處理函數
            return; // 處理完 Escape 後退出
        }
         // 在選曲畫面按 Escape 也可以做點什麼，比如退出全屏，目前不做處理
    }

    // 遊戲按鍵 (D, F, J, K) 處理
    const keyIndex = KEY_MAPPINGS.indexOf(keyCode);
    if (keyIndex !== -1) { // 如果按下的鍵是遊戲鍵之一
        // 防止按住鍵重複觸發判定 (只在按鍵狀態從 false 變為 true 時處理)
        if (!keyStates[keyCode]) {
            keyStates[keyCode] = true; // 更新按鍵狀態為按下

            // 觸發軌道閃爍特效 (無論是否判定成功，只要按下對應軌道鍵就閃爍)
            if (isPlaying && gameLoopRunning) { // 只在遊戲運行時觸發視覺特效
                 // 添加一個新的軌道閃爍效果到列表中
                 activeLaneFlashes.push({ laneIndex: keyIndex, startTime: currentSongTime, duration: LANE_FLASH_DURATION });
            }


            // 處理音符判定
            // 只有在音樂播放、遊戲迴圈運行、當前時間有效且基礎分數已計算時才進行判定
            if (isPlaying && gameLoopRunning && currentSongTime > 0 && baseScorePerPerfect >= 0) {
                const pressTime = currentSongTime; // 按鍵觸發時的歌曲時間

                let bestNote = null; // 找到的最適合判定的音符
                let minTimeDiff = Infinity; // 找到的最適合判定的音符的時間差

                // 遍歷所有載入的音符來尋找符合條件的音符進行判定
                loadedNotes.forEach(note => {
                    // 只檢查屬於正確軌道且尚未被判定的音符
                    // 音符是否活躍 (在屏幕內) 由繪圖邏輯處理，判定邏輯只關心時間和狀態
                    if (note.column === keyIndex && !note.judged) {
                        const timeDiff = pressTime - note.targetTime; // 計算按鍵時間與音符目標時間的時間差

                        // 在 Miss 窗口的範圍內尋找時間差絕對值最小的音符
                        if (Math.abs(timeDiff) <= JUDGE_WINDOW_MISS) {
                             // 如果找到一個更接近目標時間的音符，更新 bestNote
                            if (Math.abs(timeDiff) < Math.abs(minTimeDiff)) {
                                minTimeDiff = timeDiff;
                                bestNote = note;
                            }
                        }
                    }
                });

                // 如果找到了最佳匹配的音符 (在 Miss 窗口內)
                if (bestNote) {
                    const absTimeDiff = Math.abs(minTimeDiff);
                    let judgmentText = ''; // 判定結果文字
                    let scoreToAdd = 0; // 本次判定增加的分數
                    let particleCount = 0; // 特效粒子數量
                    let particleColor = ''; // 特效粒子顏色
                    let shockwaveColor = ''; // 衝擊波顏色

                    // 根據時間差判斷 Perfect, Great, Good
                    if (absTimeDiff <= JUDGE_WINDOW_PERFECT) {
                        judgmentText = 'Perfect';
                        scoreToAdd = baseScorePerPerfect;
                        combo++; // 增加連擊
                        judgmentCounts.perfect++; // 增加 Perfect 計數
                        particleCount = PARTICLE_COUNT_PERFECT;
                        particleColor = COLOR_PERFECT_PARTICLE;
                        shockwaveColor = COLOR_SHOCKWAVE_PERFECT;
                    } else if (absTimeDiff <= JUDGE_WINDOW_GREAT) {
                        judgmentText = 'Great';
                        scoreToAdd = baseScorePerPerfect * 0.5; // Great 分數
                        combo++; // 增加連擊
                        judgmentCounts.great++; // 增加 Great 計數
                        particleCount = PARTICLE_COUNT_GREAT;
                        particleColor = COLOR_GREAT_PARTICLE;
                        shockwaveColor = COLOR_SHOCKWAVE_GREAT;
                    } else if (absTimeDiff <= JUDGE_WINDOW_GOOD) {
                        judgmentText = 'Good';
                        scoreToAdd = baseScorePerPerfect * 0.3; // Good 分數
                        combo++; // 增加連擊
                        judgmentCounts.good++; // 增加 Good 計數
                        particleCount = PARTICLE_COUNT_GOOD;
                        particleColor = COLOR_GOOD_PARTICLE;
                        shockwaveColor = COLOR_SHOCKWAVE_GOOD;
                    }
                     // 注意：這裡只處理 Perfect/Great/Good。Miss 是由 gameLoop 處理音符超時產生的。

                    // 如果判定成功 (Perfect, Great, 或 Good)
                    if (judgmentText) {
                         console.log(`判定: ${judgmentText} (分數: ${scoreToAdd.toFixed(2)}) Combo: ${combo} (時間差: ${minTimeDiff.toFixed(3)}s) Note ID: ${bestNote.id}`);

                         // 標記音符為已判定，不再參與後續判定和 Miss 檢測或位置更新
                         bestNote.judged = true;
                         bestNote.isActive = false; // 判定後立即設為不活躍 (停止繪製)

                         // 更新最近判定文字顯示
                         lastJudgment = { text: judgmentText, time: currentSongTime, column: keyIndex };

                         // 更新總分數
                         score += scoreToAdd;
                         // 更新最大連擊數
                         maxCombo = Math.max(maxCombo, combo);

                         // 播放打擊音效
                         playKeysound();

                         // 觸發視覺特效
                         const hitCenterX = getInterpolatedX(keyIndex + 0.5, JUDGMENT_LINE_Y); // 判定點的 X 座標 (軌道中心)
                         const hitCenterY = JUDGMENT_LINE_Y; // 判定點的 Y 座標
                         const laneWidthAtJudgment = getInterpolatedX(keyIndex + 1, JUDGMENT_LINE_Y) - getInterpolatedX(keyIndex, JUDGMENT_LINE_Y); // 判定線處的軌道寬度

                         // 添加粒子效果
                         const newParticleEffect = { type: judgmentText, particles: [] };
                         for (let i = 0; i < particleCount; i++) {
                            const angle = Math.random() * Math.PI * 2; // 隨機方向
                            const speed = PARTICLE_BASE_SPEED + Math.random() * PARTICLE_RANDOM_SPEED; // 隨機速度
                            const lifetime = PARTICLE_MIN_LIFETIME + Math.random() * (PARTICLE_MAX_LIFETIME - PARTICLE_MIN_LIFETIME); // 隨機生命週期
                            const size = PARTICLE_BASE_SIZE + Math.random() * PARTICLE_RANDOM_SIZE; // 隨機大小
                            const angularVelocity = (Math.random() - 0.5) * 2 * PARTICLE_ANGULAR_VELOCITY_RANGE; // 隨機角速度
                            newParticleEffect.particles.push({
                                x: hitCenterX, y: hitCenterY, // 初始位置在判定點
                                vx: Math.cos(angle) * speed, // X 速度
                                vy: Math.sin(angle) * speed, // Y 速度
                                rotation: Math.random() * Math.PI * 2, // 初始旋轉角度
                                angularVelocity: angularVelocity,
                                size: size,
                                color: particleColor,
                                alpha: 1.0, // 初始透明度
                                startTime: currentSongTime, // 特效開始時間
                                lifetime: lifetime // 特效持續時間
                            });
                         }
                         activeHitEffects.push(newParticleEffect); // 將新的粒子效果添加到列表中

                         // 添加光環效果
                         activeRingEffects.push({
                            centerX: hitCenterX,
                            centerY: hitCenterY,
                            startWidth: laneWidthAtJudgment, // 光環起始大小基於軌道寬度
                            startTime: currentSongTime,
                            duration: RING_EFFECT_DURATION
                         });

                         // 添加衝擊波效果
                         activeShockwaves.push({
                            centerX: hitCenterX,
                            centerY: hitCenterY,
                            startWidth: laneWidthAtJudgment, // 衝擊波起始大小基於軌道寬度
                            startTime: currentSongTime,
                            duration: SHOCKWAVE_DURATION,
                            color: shockwaveColor
                         });

                         // 添加判定線脈衝效果
                         activeJudgmentLinePulses.push({
                            startTime: currentSongTime,
                            duration: JUDGMENT_LINE_PULSE_DURATION
                         });

                         // 添加垂直光束特效
                         // 光束對象只需要記錄軌道、開始時間和持續時間
                         activeLaneBeams.push({
                            laneIndex: keyIndex, // 記錄是哪一軌道
                            startTime: currentSongTime,
                            duration: BEAM_DURATION
                         });


                    } else {
                         // 如果找到了 bestNote，但時間差超過 Good 窗口 (即落在了 Miss 範圍內，但不是超時)
                         // 這種情況下，我們讓遊戲迴圈的超時 Miss 邏輯來處理它。
                         // 所以這裡不需要做 Miss 判定或清零連擊。
                         console.log(`按鍵時機過差，未命中有效判定窗口 (時間差: ${minTimeDiff.toFixed(3)}s) Note ID: ${bestNote.id}`);
                         // 可以選擇在這裡觸發一個視覺或聽覺提示，表示空判或太差
                         playKeysound(); // 即使沒判定上也可以選擇播放打擊音效
                         // 可以觸發一個無判定結果的特效 (例如一個更弱的軌道閃爍或光環)
                         // 軌道閃爍已經在上面觸發過了。
                    }
                } else {
                    // 如果根本沒有找到 bestNote (該軌道沒有未判定的音符在 Miss 窗口內)
                    console.log(`空敲 Lane ${keyIndex + 1} (時間: ${currentSongTime.toFixed(3)}s)`);
                    // 空敲也可以觸發一個視覺或聽覺反饋
                    playKeysound(); // 空敲時也播放打擊音效
                     // 軌道閃爍已經在上面觸發過了。
                }
            }
        }
    }
});


window.addEventListener('keyup', function(event) {
    const keyCode = event.code;
    // 只有遊戲相關鍵才更新狀態
    if (KEY_MAPPINGS.includes(keyCode)) {
        if (keyStates[keyCode]) {
            keyStates[keyCode] = false; // 更新按鍵狀態為未按下
        }
    }
});


function handleSongSelect(event) {
    if (gameState !== 'SELECTING') {
        console.warn("Attempted song selection while not in SELECTING state.");
        return; // 只在選曲狀態下允許選歌
    }

    const songItem = event.currentTarget; // 獲取被點擊的歌曲項目元素
    // 從 dataset 中獲取歌曲 ID，然後從 availableSongs 列表中找到對應的歌曲數據
    const songData = availableSongs.find(song => song.id === songItem.dataset.songId);

    if (songData) {
        startGame(songData); // 使用找到的歌曲數據開始遊戲
    } else {
        console.error("選中的歌曲數據無效！", songItem.dataset);
        alert("選擇的歌曲資料似乎有問題，請稍後再試。");
         // 即使數據無效，保持在選曲畫面
    }
}

// 窗口大小改變時重新調整 Canvas
let resizeTimeout;
window.addEventListener('resize', () => {
    // 使用 debounce 防止頻繁觸發 resize
    clearTimeout(resizeTimeout);
    resizeTimeout = setTimeout(() => {
        resizeCanvas(); // 調整 Canvas 大小和遊戲參數
         // 在非遊戲狀態下，resizeCanvas 內部會調用 drawGameBackground
         // 在遊戲狀態下，gameLoop 會處理繪製，所以這裡不需要額外調用 drawGameBackground
    }, 100); // 延遲 100ms
});


function handleBackToSelectClick() {
    console.log(`返回按鈕/Escape 觸發... 當前狀態: ${gameState}`);
    const currentState = gameState;

    // 取消待處理的遊戲開始延遲定時器 (如果存在)
    if (gameStartDelayTimeoutId) {
        console.log("取消待處理的遊戲開始延遲。");
        clearTimeout(gameStartDelayTimeoutId);
        gameStartDelayTimeoutId = null;
    }

    // 定義一個清理並返回選單的函數
    const cleanupAndGoToSelect = () => {
        console.log("執行清理並返回選單...");
        // 停止遊戲音訊 (如果正在播放)
        if (isPlaying) {
            if (audioSource) {
                try { audioSource.stop(); } catch(e) {console.warn("停止音源時出錯(可能已停止):", e);}
                audioSource.disconnect();
                audioSource = null;
            }
            isPlaying = false;
        }
        // 停止遊戲迴圈
        gameLoopRunning = false;

        // 重置所有遊戲相關的載入和運行狀態以及數據
        isAudioLoading = false;
        isAudioReady = false;
        isChartLoading = false;
        isChartReady = false;
        audioBuffer = null;
        chartData = null;
        loadedNotes = [];
        totalNotesInChart = 0;
        baseScorePerPerfect = 0;
        selectedSongData = null; // 清空選中的歌曲數據

        // 清理特效列表
        activeHitEffects = [];
        activeLaneFlashes = [];
        activeRingEffects = [];
        activeShockwaves = [];
        activeJudgmentLinePulses = [];
        activeLaneBeams = []; // 清空垂直光束特效

        // 重置背景圖和遊戲內小曲繪狀態
        songBgImage = null; isSongBgLoading = false; isSongBgReady = false;
        gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;

         // 重置分數和判定計數 (結算畫面的數據，返回選單時清空)
        score = 0; combo = 0; maxCombo = 0;
        judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };
        lastJudgment = { text: '', time: 0, column: -1 };

        // 切換到選曲畫面
        showScreen('SELECTING');
    };

    // 根據當前狀態決定如何返回，可能需要等待淡出動畫
    switch (currentState) {
        case 'RESULT':
            console.log("從結算畫面返回，開始淡出...");
            // 觸發結算畫面淡出
            resultScreen.classList.remove('visible');
            // 等待淡出完成後執行清理和狀態切換
            setTimeout(cleanupAndGoToSelect, 500); // 假設淡出動畫時間為 500ms
            break;
        case 'INTRO':
            console.log("從 Intro 畫面返回，開始淡出...");
            // 觸發 Intro 畫面淡出
            introScreen.classList.remove('visible');
             // 等待淡出完成後執行清理和狀態切換
            setTimeout(cleanupAndGoToSelect, 500); // 假設淡出動畫時間為 500ms
            break;
        case 'LOADING':
            console.log("從載入畫面返回...");
             // 載入畫面通常沒有淡出動畫，直接清理並切換
            cleanupAndGoToSelect();
            break;
        case 'PLAYING':
        case 'GAME':
            console.log("從遊戲中返回...");
            // 遊戲中直接清理並切換
            // **修改點：修正函數名稱 typo**
            cleanupAndGoToSelect(); // 原來是 cleanupAndToSelect()
            break;
        case 'SELECTING':
            console.log("已經在選單畫面，無需操作。");
            break;
        default:
            console.log(`在 ${currentState} 狀態下觸發返回，未定義明確操作，執行預設清理。`);
            cleanupAndGoToSelect(); // 對於未知狀態，執行默認清理
            break;
    }
}


// =============================================================================
// 速度控制函數
// =============================================================================
function updateSpeedDisplay() {
    if (speedDisplay) {
        speedDisplay.textContent = `x${speedMultiplier.toFixed(2)}`; // 顯示當前速度，保留兩位小數
    }
}

function increaseSpeed() {
    if (speedMultiplier < MAX_SPEED_MULTIPLIER) {
        // 增加速度，並確保浮點數計算精度
        speedMultiplier = parseFloat((speedMultiplier + SPEED_ADJUST_STEP).toFixed(2));
        // 重新計算音符出現偏移時間，速度越快偏移時間越短
        noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier;
        updateSpeedDisplay(); // 更新速度顯示
        console.log(`速度增加到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`);
    } else {
        console.log("已達到最大速度");
    }
}

function decreaseSpeed() {
    if (speedMultiplier > MIN_SPEED_MULTIPLIER) {
         // 減少速度，並確保浮點數計算精度
        speedMultiplier = parseFloat((speedMultiplier - SPEED_ADJUST_STEP).toFixed(2));
         // 確保速度不低於最小值
        speedMultiplier = Math.max(MIN_SPEED_MULTIPLIER, speedMultiplier);
        // 重新計算音符出現偏移時間
        noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier;
        updateSpeedDisplay(); // 更新速度顯示
        console.log(`速度減少到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`);
    } else {
        console.log("已達到最小速度");
    }
}


// =============================================================================
// Splash Screen 處理函數
// =============================================================================
function initializeAudioContext() {
    // 只有在 AudioContext 不存在時才創建
    if (!audioContext) {
        try {
            audioContext = new AudioContext();
            console.log("AudioContext 初始化成功。");

            // 檢查初始狀態，如果 suspended，嘗試恢復 (有些瀏覽器需要用戶互動後才能啟動 AC)
            if (audioContext.state === 'suspended') {
                console.warn("AudioContext 初始狀態為 suspended，嘗試恢復...");
                audioContext.resume().then(() => {
                    console.log("AudioContext 已成功恢復！");
                }).catch(err => {
                    console.error("自動恢復 AudioContext 失敗:", err);
                    // alert("無法自動啟用音訊。如果遊戲無聲，請嘗試重新載入或檢查瀏覽器設定。"); // 避免彈窗打斷首次體驗
                });
            }
        } catch (e) {
            console.error("無法創建 AudioContext:", e);
            alert("無法初始化音訊系統。您的瀏覽器可能不支援或已禁用 Web Audio API。");
        }
    } else if (audioContext.state === 'suspended') {
        // 如果已經存在但處於 suspended，再次嘗試恢復 (比如用戶點擊了其他地方又點回來)
        console.warn("AudioContext 處於 suspended 狀態，嘗試恢復...");
        audioContext.resume().catch(err => {
            console.error("恢復已存在的 AudioContext 失敗:", err);
             // alert("無法啟用音訊。請嘗試重新整理頁面或檢查瀏覽器設定。"); // 避免彈窗
        });
    } else {
        console.log("AudioContext 已存在且狀態為:", audioContext.state);
    }
}

function handleSplashScreenClick() {
    console.log("Splash Screen 被點擊。");

    // 點擊 Splash Screen 時初始化並嘗試恢復 AudioContext
    initializeAudioContext();

    // 觸發 Splash Screen 淡出動畫
    const splashFadeOutDuration = 500; // CSS 中定義的過渡時間
    if (splashScreen) {
        splashScreen.classList.remove('visible'); // 移除 visible 觸發淡出
        console.log("開始淡出 Splash Screen...");

        // 等待淡出動畫完成後隱藏 Splash Screen 並切換到選曲畫面
        setTimeout(() => {
            console.log("Splash Screen 淡出完成。");
            if (splashScreen) {
                splashScreen.classList.add('hidden'); // 完全隱藏
            }

            // 在淡出和顯示選單之間加入短暫黑屏，增加過渡效果
            const blackScreenDuration = 300; // 黑屏持續時間
            console.log(`保持黑畫面 ${blackScreenDuration}ms...`);

            setTimeout(() => {
                console.log("黑畫面結束，顯示選曲畫面...");
                showScreen('SELECTING'); // 切換到選曲畫面
            }, blackScreenDuration);

        }, splashFadeOutDuration);
    } else {
         console.error("無法找到 Splash Screen 元素，直接跳轉到選曲。");
         showScreen('SELECTING');
    }

}


// =============================================================================
// 應用程式初始化與啟動
// =============================================================================
async function initializeApp() {
    console.log("應用程式初始化...");

    // 初始調整 Canvas 大小
    resizeCanvas();

    // 設置 Splash Screen 的初始狀態和點擊監聽器
    if (splashScreen) {
        // 確保 splashScreen 是可見的 (雖然 CSS 設置了 opacity: 0)
        splashScreen.classList.remove('hidden');
        // 添加 visible class 觸發可能的淡入 (如果初始 opacity 為 0)
        splashScreen.classList.add('visible'); // 添加 visible 觸發初始淡入
        splashScreen.style.opacity = 1; // 強制設置 opacity 1
        // 使用 once: true 確保點擊監聽器只觸發一次
        splashScreen.addEventListener('click', handleSplashScreenClick, { once: true });
        console.log("Splash Screen 已顯示並設定點擊監聽器。");
    } else {
        console.error("找不到 Splash Screen 元素！應用程式啟動流程中斷。");
        alert("致命錯誤：頁面初始化失敗，無法找到 Splash 畫面。");
        return;
    }

    // 在載入歌曲列表前顯示提示信息
    if (songListContainer) {
        songListContainer.innerHTML = '<p>正在載入歌曲列表...</p>';
    } else {
         console.error("找不到歌曲列表容器！");
    }


    // 載入歌曲列表
    try {
        const response = await fetch('songlist.json');
        if (!response.ok) throw new Error(`無法載入 songlist.json: ${response.statusText}`);
        availableSongs = await response.json();
        console.log(`歌曲列表載入完成，共 ${availableSongs.length} 首歌。`);
        // 使用載入的歌曲列表填充選曲畫面
        // 只有當前狀態為 SPLASH 時才填充，防止過早操作 DOM
        if (gameState === 'SPLASH') {
             populateSongList();
        } else {
             console.warn(`歌曲列表載入完成，但當前狀態不是 SPLASH (${gameState})，延遲填充列表。`);
             // 可以考慮在進入 SELECTING 狀態時再次檢查並填充列表
             // 或者當切換到 SELECTING 時總是調用 populateSongList()
        }

    } catch (error) {
        console.error("應用程式初始化失敗 (載入歌曲列表時):", error);
        // 顯示錯誤信息在歌曲列表容器中
        if (songListContainer) songListContainer.innerHTML = `<p style="color: red;">錯誤：無法載入歌曲列表。<br>${error.message}</p>`;
        availableSongs = []; // 確保 availableSongs 為空陣列
    }

    // 為速度控制按鈕添加事件監聽器
    if (increaseSpeedButton && decreaseSpeedButton) {
        increaseSpeedButton.addEventListener('click', increaseSpeed);
        decreaseSpeedButton.addEventListener('click', decreaseSpeed);
        updateSpeedDisplay(); // 更新初始速度顯示
    } else {
        console.error("無法找到速度控制按鈕元素！");
    }

    // 返回選單按鈕的監聽器，綁定一次即可，通過狀態控制行為
    const backButton = document.getElementById('back-to-select-button');
     if (backButton) {
         backButton.addEventListener('click', handleBackToSelectClick);
     } else {
         console.error("找不到返回選單按鈕！");
     }

    // 初始繪製背景，即使在 Splash 畫面也要有背景
    // resizeCanvas 會調用 drawGameBackground，所以在 resizeCanvas 後再畫一次確保
    drawGameBackground();
}

// 等待 DOM 載入完成後初始化應用程式
window.addEventListener('DOMContentLoaded', initializeApp);