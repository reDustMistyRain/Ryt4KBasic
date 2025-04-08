"use strict";
console.log("遊戲腳本開始執行...");

// =============================================================================
// DOM 元素獲取與檢查
// =============================================================================
const appContainer = document.getElementById('app-container');
const splashScreen = document.getElementById('splash-screen'); // *** 新增：獲取 Splash Screen ***
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

// Check for essential elements, now including splashScreen
if (!canvas || !ctx || !appContainer || !splashScreen || !songSelectScreen || !songListContainer || !resultScreen || !introScreen || !introIllustration || !introTitle || !introArtist || !resultIllustration || !resultTitle || !resultArtist || !speedDisplay || !increaseSpeedButton || !decreaseSpeedButton) {
    console.error("錯誤：無法找到必要的 HTML 元素！請確保 index.html 包含所有需要的 ID。");
    alert("頁面初始化錯誤！缺少必要的元素。");
    throw new Error("Missing critical HTML elements.");
}

// =============================================================================
// 遊戲狀態管理
// =============================================================================
let gameState = 'SPLASH'; // Initial state is now the splash screen
let availableSongs = [];
let selectedSongData = null;
let gameStartDelayTimeoutId = null; // Stores the timeout ID for the game start delay

// =============================================================================
// 遊戲核心參數與設定
// =============================================================================
const LANE_COUNT = 4; 
let JUDGMENT_LINE_Y = 0; 
let PERSPECTIVE_STRENGTH = 0.8;
let TOP_TOTAL_WIDTH = 0; 
let TOP_OFFSET_X = 0; 
let BOTTOM_LANE_WIDTH = 0; 
let TOP_LANE_WIDTH = 0;
const START_DELAY_SECONDS = 1.1; // Delay before *music* starts after scheduled time (增加到1.1秒讓音樂晚1秒開始)
const INTRO_TO_GAME_DELAY_SECONDS = 2.0; // Delay after intro fades out before game starts
const ADDITIONAL_NOTE_OFFSET_SECONDS = 1.0; // 額外的音符提前出現時間偏移量 (讓音符提前1秒出現)
const BASE_NOTE_APPEAR_TIME_OFFSET = 2.0;
let speedMultiplier = 1.0;
let noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier;
const MIN_SPEED_MULTIPLIER = 0.5;
const MAX_SPEED_MULTIPLIER = 5.0;
const SPEED_ADJUST_STEP = 0.25;
const NOTE_HEIGHT_RATIO = 0.03; let NOTE_HEIGHT = 20;
const NOTE_SPEED_EASING_POWER = 2.2; const LINEAR_MIX_FACTOR = 0.15;

// =============================================================================
// 字體設定
// =============================================================================
const FONT_FAMILY_CANVAS = "'IBM Plex Mono', monospace";

// =============================================================================
// 顏色定義
// =============================================================================
const COLOR_BACKGROUND = '#000000';           // 預設背景色
const COLOR_LINES = '#FFFFFF';                // 邊界線顏色
const COLOR_LANE_SEPARATOR = '#CCCCCC';       // 軌道分隔線顏色
const COLOR_JUDGMENT_LINE = '#FFFFFF';        // 判定線顏色
const COLOR_NOTE = '#CCFFFF';                 // 音符顏色 (白青色)
const COLOR_PERFECT_PARTICLE = 'rgba(255, 215, 0,';  // Perfect 特效顏色 (金黃色)
const COLOR_GREAT_PARTICLE = 'rgba(144, 238, 144,';  // Great 特效顏色 (淺綠色)
const COLOR_GOOD_PARTICLE = 'rgba(173, 216, 230,';   // Good 特效顏色 (淺藍色)
const COLOR_LANE_FLASH = 'rgba(173, 216, 230,';      // 軌道閃光顏色 (淺藍色)
const COLOR_RING_EFFECT = 'rgba(255, 255, 255,';     // 環形特效顏色 (白色)

// =============================================================================
// 判定與計分系統 (1 Million Score System)
// =============================================================================
// 判定時間窗口 (單位：秒)
const JUDGE_WINDOW_PERFECT = 0.100; 
const JUDGE_WINDOW_GREAT = 0.200; 
const JUDGE_WINDOW_GOOD = 0.300; 
const JUDGE_WINDOW_MISS = 0.400;
const JUDGMENT_DISPLAY_DURATION = 0.5;

// 判定與分數相關變數
let lastJudgment = { text: '', time: 0, column: -1 }; 
let score = 0; 
let combo = 0; 
let maxCombo = 0;
const MAX_SCORE = 1000000;
let totalNotesInChart = 0; let baseScorePerPerfect = 0;
let judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };

// =============================================================================
// 按鍵與音訊狀態
// =============================================================================
// 按鍵映射與狀態
const KEY_MAPPINGS = ['KeyD', 'KeyF', 'KeyJ', 'KeyK']; 
const keyStates = {'KeyD': false, 'KeyF': false, 'KeyJ': false, 'KeyK': false};

// 音訊相關變數
const AudioContext = window.AudioContext || window.webkitAudioContext; 
let audioContext; 
let audioBuffer = null; 
let audioSource = null;
let audioStartTime = 0; 
let currentSongTime = 0; 
let rawElapsedTime = -START_DELAY_SECONDS;
let isAudioLoading = false; 
let isAudioReady = false; 
let isPlaying = false; 
let gameLoopRunning = false;

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
const PARTICLE_COUNT_PERFECT = 12; const PARTICLE_COUNT_GREAT = 8; const PARTICLE_COUNT_GOOD = 5;
const PARTICLE_BASE_SPEED = 100; const PARTICLE_RANDOM_SPEED = 100;
const PARTICLE_BASE_SIZE = 40; const PARTICLE_RANDOM_SIZE = 10;
const PARTICLE_MIN_LIFETIME = 0.3; const PARTICLE_MAX_LIFETIME = 0.6;
const PARTICLE_ANGULAR_VELOCITY_RANGE = Math.PI * 2;
const LANE_FLASH_DURATION = 0.15;
const RING_EFFECT_DURATION = 0.3; const RING_EFFECT_START_SCALE = 0.2;
const RING_EFFECT_END_SCALE = 1.5; const RING_EFFECT_LINE_WIDTH = 3;

// =============================================================================
// 遊戲內小曲繪狀態
// =============================================================================
let gameInfoIllustration = null;
let gameInfoIllustrationSrc = '';
let gameInfoIllustrationLoaded = false;

// =============================================================================
// 初始化與狀態重置
// =============================================================================
function initializeGameState() {
    loadedNotes.forEach(note => { note.isActive = false; note.y = 0; note.judged = false; note.judgment = ''; });
    score = 0; combo = 0; maxCombo = 0;
    lastJudgment = { text: '', time: 0, column: -1 };
    judgmentCounts = { perfect: 0, great: 0, good: 0, miss: 0 };
    activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = [];
    // Reset song-specific background and game info illustration states
    songBgImage = null; isSongBgLoading = false; isSongBgReady = false;
    gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;
    // Cancel any pending game start delay
    if (gameStartDelayTimeoutId) { clearTimeout(gameStartDelayTimeoutId); gameStartDelayTimeoutId = null; }
    console.log("遊戲狀態已重置 (分數, 特效, 曲繪狀態等)。");
}

// =============================================================================
// 輔助函式
// =============================================================================
/**
 * 計算透視效果下的 X 座標
 * @param {number} boundaryIndex - 軌道邊界索引
 * @param {number} y - Y 座標位置
 * @returns {number} - 計算後的 X 座標
 */
function getInterpolatedX(boundaryIndex, y) { 
    // 檢查必要參數是否已初始化
    if (BOTTOM_LANE_WIDTH === undefined || TOP_LANE_WIDTH === undefined || 
        TOP_OFFSET_X === undefined || canvas.height <= 0) {
        return 0;
    }
    
    // 計算底部和頂部的 X 座標
    const bottomX = boundaryIndex * BOTTOM_LANE_WIDTH;
    const topX = TOP_OFFSET_X + (boundaryIndex * TOP_LANE_WIDTH);
    
    // 確保 Y 值在有效範圍內
    const clampedY = Math.max(0, Math.min(canvas.height, y));
    
    // 計算插值比例
    const ratio = canvas.height > 0 ? (clampedY / canvas.height) : 0;
    
    // 返回插值後的 X 座標
    return topX + (bottomX - topX) * ratio;
}

/**
 * 調整畫布大小並重新計算相關參數
 */
function resizeCanvas() {
    const displayWidth = window.innerWidth;
    const displayHeight = window.innerHeight;
    
    // 只有當尺寸變化超過閾值時才調整
    if (Math.abs(canvas.width - displayWidth) > 1 || Math.abs(canvas.height - displayHeight) > 1) {
        canvas.width = displayWidth;
        canvas.height = displayHeight;
        console.log(`Canvas resized to: ${canvas.width} x ${canvas.height}`);
        
        // 重新計算遊戲參數
        JUDGMENT_LINE_Y = canvas.height * 0.85;
        TOP_TOTAL_WIDTH = canvas.width * (1 - PERSPECTIVE_STRENGTH);
        TOP_OFFSET_X = (canvas.width - TOP_TOTAL_WIDTH) / 2;
        BOTTOM_LANE_WIDTH = canvas.width / LANE_COUNT;
        TOP_LANE_WIDTH = TOP_TOTAL_WIDTH / LANE_COUNT;
        NOTE_HEIGHT = Math.max(10, Math.round(canvas.height * NOTE_HEIGHT_RATIO));
        
        console.log(`重新計算參數: 判定線 Y=${JUDGMENT_LINE_Y.toFixed(0)}, 音符高度=${NOTE_HEIGHT}`);
        
        // 在特定條件下重繪背景
        if (!gameLoopRunning && ctx && 
            gameState !== 'LOADING' && 
            gameState !== 'INITIALIZING' && 
            gameState !== 'SELECTING' && 
            gameState !== 'SPLASH') {
            drawGameBackground();
        }
    }
}
/**
 * 繪製遊戲背景
 * 包括背景圖片、模糊效果和暗化處理
 */
function drawGameBackground() {
    if (!ctx) return;
    
    // 清除畫布
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    // 如果背景圖已準備好，繪製背景圖
    if (isSongBgReady && songBgImage) {
        // 設置模糊效果
        ctx.filter = `blur(${BACKGROUND_BLUR_AMOUNT}px)`;
        
        // 計算圖片與畫布的比例
        const canvasAspect = canvas.width / canvas.height;
        const bgAspect = songBgImage.naturalWidth / songBgImage.naturalHeight;
        let drawWidth, drawHeight, offsetX = 0, offsetY = 0;
        
        // 根據比例調整繪製尺寸和位置
        if (bgAspect > canvasAspect) {
            drawHeight = canvas.height;
            drawWidth = drawHeight * bgAspect;
            offsetX = (canvas.width - drawWidth) / 2;
        } else {
            drawWidth = canvas.width;
            drawHeight = drawWidth / bgAspect;
            offsetY = (canvas.height - drawHeight) / 2;
        }
        
        // 嘗試繪製背景圖
        try {
            ctx.drawImage(songBgImage, offsetX, offsetY, drawWidth, drawHeight);
        } catch (e) {
            console.error("繪製背景圖時出錯:", e);
            isSongBgReady = false;
            songBgImage = null;
            ctx.fillStyle = COLOR_BACKGROUND;
            ctx.fillRect(0, 0, canvas.width, canvas.height);
        }
        
        // 重置濾鏡並添加暗化效果
        ctx.filter = 'none';
        ctx.fillStyle = `rgba(0, 0, 0, ${BACKGROUND_DIM_ALPHA})`;
        ctx.fillRect(0, 0, canvas.width, canvas.height);
    } else {
        // 如果沒有背景圖，使用純色背景
        ctx.fillStyle = COLOR_BACKGROUND;
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        // 如果需要且尚未載入，嘗試載入背景圖
        if (!isSongBgLoading && !isSongBgReady && 
            selectedSongData?.illustrationPath && 
            (gameState === 'LOADING' || gameState === 'GAME' || gameState === 'PLAYING')) {
            loadSongBackgroundImage(selectedSongData.illustrationPath);
        }
    }
    
    // 在遊戲狀態下繪製透視元素
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
    allOverlays.forEach(screen => screen.classList.add('hidden'));

    if (screenId === 'GAME') { canvas.classList.remove('hidden'); console.log("[showScreen] Canvas 設為可見"); }
    else { canvas.classList.add('hidden'); console.log(`[showScreen] Canvas 設為隱藏 (狀態: ${screenId})`); }

    switch (screenId) {
        case 'SPLASH': targetOverlayScreen = splashScreen; break;
        case 'SELECTING':
            targetOverlayScreen = songSelectScreen;
            if (isPlaying || gameLoopRunning) {
                if (audioSource) { try { audioSource.stop(); } catch(e){} audioSource.disconnect(); }
                isPlaying = false; audioSource = null; gameLoopRunning = false;
                if (gameStartDelayTimeoutId) { clearTimeout(gameStartDelayTimeoutId); gameStartDelayTimeoutId = null; }
                // Only reset game-specific state, not score/judgments needed for result screen
                loadedNotes = []; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = [];
            }
            isAudioReady = false; isChartReady = false;
            selectedSongData = null; chartData = null; audioBuffer = null;
            songBgImage = null; isSongBgLoading = false; isSongBgReady = false;
            gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false;
            totalNotesInChart = 0; baseScorePerPerfect = 0;
            console.log("準備進入選曲畫面並重置遊戲資源");
            break;
        case 'RESULT': targetOverlayScreen = resultScreen; break;
        case 'INTRO': targetOverlayScreen = introScreen; break;
        case 'GAME': case 'LOADING': case 'INITIALIZING': targetOverlayScreen = null; break;
        default: console.error("未知的畫面 ID:", screenId); targetOverlayScreen = songSelectScreen; screenId = 'SELECTING'; break;
    }
    gameState = screenId;
    if (targetOverlayScreen) {
        targetOverlayScreen.classList.remove('hidden');
        console.log(`[showScreen] ${targetOverlayScreen.id} 畫面已移除 hidden`);
        requestAnimationFrame(() => { setTimeout(() => { if (gameState === screenId) { targetOverlayScreen.classList.add('visible'); console.log(`[showScreen] ${targetOverlayScreen.id} (${screenId}) set to visible`); } else { console.log(`[showScreen] State changed (${gameState}) before ${targetOverlayScreen.id} (${screenId}) could become visible.`); } }, 50); });
    } else { console.log(`[showScreen] ${screenId} 狀態，無特定疊加畫面。`); }

    console.log(`[showScreen] 狀態從 ${previousState} 切換到: ${gameState}`);
    if (screenId !== 'GAME' && !gameLoopRunning) { if (canvas.width === 0 || canvas.height === 0) resizeCanvas(); drawGameBackground(); }
}
function populateSongList() { if (!songListContainer) return; songListContainer.innerHTML = ''; if (availableSongs.length === 0) { songListContainer.innerHTML = '<p>未找到歌曲。</p>'; return; } availableSongs.sort((a, b) => a.title.localeCompare(b.title)); availableSongs.forEach(song => { const songItem = document.createElement('div'); songItem.classList.add('song-item'); songItem.dataset.songId = song.id; songItem.dataset.chartPath = song.chartPath; songItem.dataset.audioPath = song.audioPath; songItem.dataset.illustrationPath = song.illustrationPath; songItem.dataset.title = song.title; songItem.dataset.artist = song.artist || '未知'; const img = document.createElement('img'); img.classList.add('song-illustration'); img.src = song.illustrationPath; img.alt = song.title; img.onerror = () => { img.src = 'placeholder.png'; }; const details = document.createElement('div'); details.classList.add('song-details'); const titleP = document.createElement('p'); titleP.classList.add('song-title'); titleP.textContent = song.title; const artistP = document.createElement('p'); artistP.classList.add('song-artist'); artistP.textContent = song.artist || '未知'; details.appendChild(titleP); details.appendChild(artistP); songItem.appendChild(img); songItem.appendChild(details); songItem.addEventListener('click', handleSongSelect); songListContainer.appendChild(songItem); }); }

// =============================================================================
// 資源載入與狀態檢查
// =============================================================================
async function loadAudio(url) { if (!audioContext || isAudioLoading || isAudioReady || !url) return; isAudioLoading = true; updateLoadingStatus(); console.log(`載入音訊: ${url}...`); try { const response = await fetch(url); if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`); const arrayBuffer = await response.arrayBuffer(); audioBuffer = await audioContext.decodeAudioData(arrayBuffer); isAudioReady = true; console.log("歌曲音訊載入完成！"); checkAndTriggerIntro(); } catch (error) { console.error(`載入音訊錯誤 (${url}):`, error); alert(`載入歌曲音訊失敗: ${url}\n${error.message}`); showScreen('SELECTING'); audioBuffer = null; isAudioReady = false; } finally { isAudioLoading = false; updateLoadingStatus(); } }
async function loadChart(url) { if (isChartLoading || isChartReady || !url) return; isChartLoading = true; updateLoadingStatus(); console.log(`載入譜面: ${url}...`); try { const response = await fetch(url); if (!response.ok) throw new Error(`無法載入譜面: ${response.statusText}`); chartData = await response.json(); if (!chartData || !chartData.notes || !chartData.metadata) throw new Error("譜面格式錯誤"); globalOffsetSeconds = (chartData.metadata.global_offset_ms || 0) / 1000.0; loadedNotes = []; chartData.notes.forEach(note => { if (note.targetTime !== undefined && note.column !== undefined) { const adjustedTargetTime = note.targetTime + globalOffsetSeconds; loadedNotes.push({ ...note, originalTargetTime: note.targetTime, targetTime: adjustedTargetTime, isActive: false, y: 0, judged: false, judgment: '' }); } else { console.warn("忽略格式不符音符:", note); } }); totalNotesInChart = loadedNotes.length; if (totalNotesInChart > 0) { baseScorePerPerfect = MAX_SCORE / totalNotesInChart; console.log(`譜面載入完成！共 ${totalNotesInChart} 音符。Perfect基礎分數: ${baseScorePerPerfect.toFixed(4)}`); } else { baseScorePerPerfect = 0; console.warn("譜面載入完成，但 Note 數量為 0！"); } isChartReady = true; checkAndTriggerIntro(); } catch (error) { console.error(`載入譜面錯誤 (${url}):`, error); alert(`載入譜面失敗: ${url}\n${error.message}`); showScreen('SELECTING'); chartData = null; loadedNotes = []; totalNotesInChart = 0; baseScorePerPerfect = 0; isChartReady = false; } finally { isChartLoading = false; updateLoadingStatus(); } }
async function loadKeysound() { if (!audioContext || isKeysoundLoading || isKeysoundReady) return; isKeysoundLoading = true; console.log(`載入打擊音效: ${KEYSOUND_PATH}...`); try { const response = await fetch(KEYSOUND_PATH); if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`); const arrayBuffer = await response.arrayBuffer(); keysoundBuffer = await audioContext.decodeAudioData(arrayBuffer); isKeysoundReady = true; console.log("打擊音效載入完成！"); } catch (error) { console.error("載入打擊音效錯誤:", error); keysoundBuffer = null; isKeysoundReady = false; } finally { isKeysoundLoading = false; } }
async function loadSongBackgroundImage(url) { if (!url) { console.warn("歌曲無背景圖路徑，使用預設背景。"); songBgImage = null; isSongBgReady = false; isSongBgLoading = false; return; } if (songBgImage && songBgImage.src.includes(url.split('/').pop()) && isSongBgReady) { console.log("歌曲背景圖似乎已載入，跳過。"); return; } isSongBgLoading = true; isSongBgReady = false; songBgImage = null; console.log(`載入歌曲背景圖: ${url}...`); updateLoadingStatus(); try { const img = new Image(); await new Promise((resolve, reject) => { img.onload = () => { songBgImage = img; isSongBgReady = true; console.log("歌曲背景圖載入完成！"); resolve(); }; img.onerror = (err) => { console.error(`載入歌曲背景圖錯誤 (${url}):`, err); songBgImage = null; isSongBgReady = false; reject(err); }; img.src = url; }); } catch (error) { /* Handled */ } finally { isSongBgLoading = false; updateLoadingStatus(); } }
function updateLoadingStatus() { if (gameState === 'LOADING') { console.log(`載入狀態: SongBG ${isSongBgLoading?'中':(isSongBgReady?'完成':'失敗/未載入')}, 音訊 ${isAudioLoading ? '中' : (isAudioReady ? '完成' : '失敗/未載入')}, 譜面 ${isChartLoading ? '中' : (isChartReady ? '完成' : '失敗/未載入')}, Keysound ${isKeysoundLoading ? '中' : (isKeysoundReady ? '完成' : '失敗/未載入')}`); } }
function checkAndTriggerIntro() { if (isAudioReady && isChartReady && gameState === 'LOADING') { console.log("音訊和譜面均已就緒，觸發 Intro..."); startIntro(); } else { console.log("等待資源中...", {isAudioReady, isChartReady, gameState}); } }

// =============================================================================
// Intro 畫面處理
// =============================================================================
function showIntroScreen() { if (!selectedSongData) { console.error("無法顯示 Intro，未選歌！"); showScreen('SELECTING'); return; } introIllustration.src = selectedSongData.illustrationPath || 'placeholder.png'; introIllustration.onerror = () => { introIllustration.src = 'placeholder.png'; }; introTitle.textContent = selectedSongData.title || '未知歌曲'; introArtist.textContent = selectedSongData.artist || '未知作曲家'; showScreen('INTRO'); console.log("Intro 顯示，3 秒後淡出..."); setTimeout(() => { if (gameState === 'INTRO') { console.log("Intro 時間到，開始淡出..."); introScreen.classList.remove('visible'); setTimeout(() => { if (gameState === 'INTRO') { console.log(`Intro 淡出完成，等待 ${INTRO_TO_GAME_DELAY_SECONDS} 秒後開始遊戲...`); gameStartDelayTimeoutId = setTimeout(() => { if (gameState === 'INTRO') { console.log("等待時間結束，開始播放..."); gameStartDelayTimeoutId = null; playAudio(); } else { console.log("遊戲開始延遲定時器觸發，但狀態已變，不播放音樂。"); gameStartDelayTimeoutId = null; } }, INTRO_TO_GAME_DELAY_SECONDS * 1000); } else { console.log("Intro 淡出定時器完成，但狀態已變。"); } }, 500); } else { console.log("Intro 主定時器觸發，但狀態已變，不執行淡出。"); } }, 3000); }
const startIntro = showIntroScreen;

// =============================================================================
// 音訊播放與遊戲流程控制
// =============================================================================
function playKeysound() { if (isKeysoundReady && keysoundBuffer && audioContext && audioContext.state === 'running') { try { const source = audioContext.createBufferSource(); source.buffer = keysoundBuffer; const gainNode = audioContext.createGain(); gainNode.gain.value = KEYSOUND_VOLUME; source.connect(gainNode); gainNode.connect(audioContext.destination); source.start(0); } catch (error) { console.error("播放打擊音效失敗:", error); } } }
function playAudio() { if (isPlaying || !audioContext || !audioBuffer || !chartData) { console.warn("無法播放歌曲，狀態或資源異常。", {isPlaying, audioContext, audioBufferExists: !!audioBuffer, chartDataExists: !!chartData }); return; } showScreen('GAME'); if (audioSource) { try { audioSource.stop(); } catch(e) { console.warn("停止舊音源時出錯(可能已停止):", e); } audioSource.disconnect(); audioSource = null; } audioSource = audioContext.createBufferSource(); audioSource.buffer = audioBuffer; audioSource.connect(audioContext.destination); const scheduledStartTime = audioContext.currentTime + START_DELAY_SECONDS; audioStartTime = scheduledStartTime; isPlaying = true; rawElapsedTime = -START_DELAY_SECONDS; currentSongTime = 0; console.log(`音樂預計開始於 AC 時間: ${audioStartTime.toFixed(3)}`); initializeGameState(); // Reset score, combo etc. BEFORE starting
audioSource.start(scheduledStartTime, 0); audioSource.onended = () => { console.log("音樂播放結束事件觸發。"); const wasPlaying = isPlaying; isPlaying = false; audioSource = null; if (wasPlaying && (gameState === 'PLAYING' || gameState === 'GAME')) { console.log("音樂自然結束，顯示結算畫面。"); showResultScreen(); } else { console.log(`音樂結束，但狀態為 ${gameState} 或非自然停止 (wasPlaying: ${wasPlaying})，不顯示結算。`); } }; if (!gameLoopRunning) { console.log("遊戲迴圈啟動..."); gameLoopRunning = true; requestAnimationFrame(gameLoop); } else { console.warn("playAudio 被調用，但 gameLoopRunning 已經是 true？") } }
function startGame(songData) { if (!songData || !songData.audioPath || !songData.chartPath) { console.error("無效歌曲數據！無法開始遊戲。"); alert("選擇的歌曲資料不完整！"); showScreen('SELECTING'); return; } selectedSongData = songData; console.log(`選中歌曲: ${selectedSongData.title}`); isAudioReady = false; isChartReady = false; audioBuffer = null; chartData = null; loadedNotes = []; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = []; isSongBgReady = false; isSongBgLoading = false; songBgImage = null; gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false; totalNotesInChart = 0; baseScorePerPerfect = 0; showScreen('LOADING'); initializeAudioContextAndLoad(); }
function initializeAudioContextAndLoad() { if (!audioContext) { console.error("AudioContext 未初始化！請確保在 handleSplashScreenClick 中初始化。"); alert("音訊系統尚未準備好，請重試。"); return; } const loadResources = async () => { console.log("AC 狀態:", audioContext.state, "準備載入資源..."); updateLoadingStatus(); const loadPromises = []; if (selectedSongData?.illustrationPath) { loadPromises.push(loadSongBackgroundImage(selectedSongData.illustrationPath)); } else { console.warn("未提供歌曲背景圖路徑。"); isSongBgReady = false; isSongBgLoading = false; songBgImage = null; } if (!isKeysoundReady && !isKeysoundLoading) { loadPromises.push(loadKeysound()); } if (selectedSongData.audioPath) { loadPromises.push(loadAudio(selectedSongData.audioPath)); } else { console.error("歌曲音訊路徑無效！"); alert("錯誤：歌曲缺少音訊檔案路徑！"); showScreen('SELECTING'); return; } if (selectedSongData.chartPath) { loadPromises.push(loadChart(selectedSongData.chartPath)); } else { console.error("歌曲譜面路徑無效！"); alert("錯誤：歌曲缺少譜面檔案路徑！"); showScreen('SELECTING'); return; } try { await Promise.all(loadPromises); console.log("所有主要資源載入 Promise 完成。"); } catch (error) { console.error("資源載入過程中出現未捕獲的錯誤 (Promise.all):", error); showScreen('SELECTING'); } finally { updateLoadingStatus(); } }; if (audioContext.state === 'suspended') { console.warn("AC 處於 suspended 狀態，嘗試恢復..."); audioContext.resume().then(() => { console.log("AC 已成功恢復！"); loadResources(); }).catch(err => { console.error("恢復 AC 失敗:", err); alert("無法啟用音訊。請嘗試與頁面互動（點擊/按鍵）或檢查瀏覽器設定。"); showScreen('SELECTING'); }); } else if (audioContext.state === 'running') { console.log("AC 已在運行中，直接載入資源。"); loadResources(); } else { console.error("AC 處於意外狀態:", audioContext.state); alert(`音訊系統狀態異常 (${audioContext.state})，無法載入歌曲。`); showScreen('SELECTING'); } }
function showResultScreen() { gameLoopRunning = false; isPlaying = false; if (audioSource) { try { audioSource.stop(); } catch(e) {} audioSource.disconnect(); audioSource = null; } let finalScore = score; if (totalNotesInChart > 0 && judgmentCounts.perfect === totalNotesInChart && judgmentCounts.great === 0 && judgmentCounts.good === 0 && judgmentCounts.miss === 0) { console.log("檢測到 All Perfect! 強制設定分數為 1,000,000。"); finalScore = MAX_SCORE; } const resultSongTitle = document.getElementById('result-title'); const resultArtist = document.getElementById('result-artist'); const resultIllustrationImg = document.getElementById('result-illustration'); const resultScore = document.getElementById('result-score'); const resultMaxCombo = document.getElementById('result-max-combo'); const resultPerfect = document.getElementById('result-perfect'); const resultGreat = document.getElementById('result-great'); const resultGood = document.getElementById('result-good'); const resultMiss = document.getElementById('result-miss'); const backButton = document.getElementById('back-to-select-button'); if (!resultScreen || !resultSongTitle || !resultArtist || !resultIllustrationImg || !resultScore || !resultMaxCombo || !resultPerfect || !resultGreat || !resultGood || !resultMiss || !backButton) { console.error("找不到結算畫面元素！"); showScreen('SELECTING'); return; } resultSongTitle.textContent = selectedSongData ? selectedSongData.title : '未知'; resultArtist.textContent = selectedSongData ? selectedSongData.artist : '未知'; resultIllustrationImg.src = selectedSongData ? selectedSongData.illustrationPath : 'placeholder.png'; resultIllustrationImg.onerror = () => { resultIllustrationImg.src = 'placeholder.png'; }; resultScore.textContent = Math.round(finalScore).toString().padStart(7, '0'); resultMaxCombo.textContent = maxCombo; resultPerfect.textContent = judgmentCounts.perfect; resultGreat.textContent = judgmentCounts.great; resultGood.textContent = judgmentCounts.good; resultMiss.textContent = judgmentCounts.miss; const newBackButton = backButton.cloneNode(true); if (backButton.parentNode) {backButton.parentNode.replaceChild(newBackButton, backButton);} else { console.warn("Could not replace back button, parent node not found");} newBackButton.addEventListener('click', handleBackToSelectClick); showScreen('RESULT'); console.log("顯示結算畫面"); }

// =============================================================================
// 繪圖函式 (Drawing Functions)
// =============================================================================
/**
 * 繪製透視效果的靜態元素
 * 包括軌道分隔線、邊界線和判定線
 */
function drawPerspectiveStaticElements() {
    if (!ctx) return;
    
    // 保存原始線寬
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
    
    // 繪製左右邊界線
    ctx.strokeStyle = COLOR_LINES;
    ctx.lineWidth = 6;
    
    // 左邊界
    ctx.beginPath();
    ctx.moveTo(getInterpolatedX(0, 0), 0);
    ctx.lineTo(getInterpolatedX(0, canvas.height), canvas.height);
    ctx.stroke();
    
    // 右邊界
    ctx.beginPath();
    ctx.moveTo(getInterpolatedX(LANE_COUNT, 0), 0);
    ctx.lineTo(getInterpolatedX(LANE_COUNT, canvas.height), canvas.height);
    ctx.stroke();
    
    // 繪製判定線
    ctx.strokeStyle = COLOR_JUDGMENT_LINE;
    ctx.lineWidth = 3;
    const judgmentLeftX = getInterpolatedX(0, JUDGMENT_LINE_Y);
    const judgmentRightX = getInterpolatedX(LANE_COUNT, JUDGMENT_LINE_Y);
    ctx.beginPath();
    ctx.moveTo(judgmentLeftX, JUDGMENT_LINE_Y);
    ctx.lineTo(judgmentRightX, JUDGMENT_LINE_Y);
    ctx.stroke();
    
    // 恢復原始線寬
    ctx.lineWidth = originalLineWidth;
}
/**
 * 繪製音符
 * 根據透視效果計算音符的位置和大小
 */
function drawNotes() {
    if (!ctx || !loadedNotes) return;
    
    ctx.fillStyle = COLOR_NOTE;
    
    loadedNotes.forEach(note => {
        // 只繪製未判定且處於活動狀態的音符
        if (!note.judged && note.isActive) {
            const topY = note.y;
            
            // 計算判定線處的寬度
            const judgmentLeftX = getInterpolatedX(note.column, JUDGMENT_LINE_Y);
            const judgmentRightX = getInterpolatedX(note.column + 1, JUDGMENT_LINE_Y);
            const widthAtJudgment = judgmentRightX - judgmentLeftX;
            
            // 計算音符頂部的位置和寬度
            const topLeftX = getInterpolatedX(note.column, topY);
            const topRightX = getInterpolatedX(note.column + 1, topY);
            const widthAtTop = topRightX - topLeftX;
            
            // 計算高度縮放比例
            const heightScale = (widthAtJudgment > 0) ? (widthAtTop / widthAtJudgment) : 1;
            const minHeightScale = 0.1;
            const clampedHeightScale = Math.max(minHeightScale, heightScale);
            
            // 計算音符的視覺高度和底部位置
            const currentVisualHeight = NOTE_HEIGHT * clampedHeightScale;
            const bottomY = topY + currentVisualHeight;
            
            // 只繪製在畫布範圍內的音符
            if (topY < canvas.height && bottomY > 0) {
                const bottomLeftX = getInterpolatedX(note.column, bottomY);
                const bottomRightX = getInterpolatedX(note.column + 1, bottomY);
                
                // 繪製音符的梯形
                ctx.beginPath();
                ctx.moveTo(topLeftX, topY);
                ctx.lineTo(topRightX, topY);
                ctx.lineTo(bottomRightX, bottomY);
                ctx.lineTo(bottomLeftX, bottomY);
                ctx.closePath();
                ctx.fill();
            }
        }
    });
}
/**
 * 繪製判定結果文字
 * 根據判定結果顯示不同顏色的文字，並隨時間淡出
 */
function drawJudgmentFeedback() { 
    if (!ctx) return; 
    
    // 只在有判定結果且在顯示時間內時繪製
    if (lastJudgment.text && currentSongTime >= 0 && 
        currentSongTime < lastJudgment.time + JUDGMENT_DISPLAY_DURATION) { 
        
        // 計算經過的時間和透明度
        const timeSinceJudgment = currentSongTime - lastJudgment.time; 
        const alpha = 1.0 - (timeSinceJudgment / JUDGMENT_DISPLAY_DURATION); 
        
        // 設置文字樣式
        ctx.font = `bold 56px ${FONT_FAMILY_CANVAS}`; 
        ctx.textAlign = 'center'; 
        
        // 根據判定結果選擇顏色
        let judgmentColor = 'rgba(255, 255, 255, '; 
        if (lastJudgment.text === 'Perfect') judgmentColor = COLOR_PERFECT_PARTICLE; 
        else if (lastJudgment.text === 'Great') judgmentColor = COLOR_GREAT_PARTICLE; 
        else if (lastJudgment.text === 'Good') judgmentColor = COLOR_GOOD_PARTICLE; 
        else if (lastJudgment.text === 'Miss') judgmentColor = 'rgba(255, 0, 0, '; 
        
        // 設置填充顏色並繪製文字
        ctx.fillStyle = judgmentColor + Math.max(0, alpha) + ')'; 
        const centerX = canvas.width / 2; 
        const feedbackY = JUDGMENT_LINE_Y - 80; 
        ctx.fillText(lastJudgment.text, centerX, feedbackY); 
    } 
}
/**
 * 繪製分數和連擊數
 * 在畫面上顯示當前分數、連擊數和最大連擊數
 */
function drawScoreAndCombo() { 
    if (!ctx) return; 
    
    // 繪製分數
    ctx.fillStyle = '#FFFFFF'; 
    ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`; 
    ctx.textAlign = 'right'; 
    ctx.fillText(Math.round(score).toString().padStart(7, '0'), canvas.width - 20, 40); 
    
    // 繪製連擊數
    if (combo > 0) { 
        ctx.font = `bold 64px ${FONT_FAMILY_CANVAS}`; 
        ctx.textAlign = 'center'; 
        const comboX = canvas.width / 2; 
        const comboY = JUDGMENT_LINE_Y - 200; 
        ctx.fillStyle = '#FFFF00'; 
        ctx.fillText(combo, comboX, comboY); 
        
        // 只有連擊數大於1時才顯示"Combos"文字
        if (combo > 1) { 
            ctx.font = `bold 32px ${FONT_FAMILY_CANVAS}`; 
            ctx.fillStyle = '#FFFFFF'; 
            ctx.fillText('Combos', comboX, comboY + 45); 
        } 
    } 
    
    // 繪製最大連擊數
    ctx.font = `bold 20px ${FONT_FAMILY_CANVAS}`; 
    ctx.fillStyle = '#CCCCCC'; 
    ctx.textAlign = 'right'; 
    ctx.fillText(`Max Combo: ${maxCombo}`, canvas.width - 20, 70); 
}
/**
 * 預載遊戲內小曲繪圖片
 * @param {string} src - 圖片路徑
 */
function preloadGameInfoIllustration(src) { 
    // 如果路徑為空或與當前路徑相同，檢查是否已載入
    if (!src || src === gameInfoIllustrationSrc) { 
        if (src === gameInfoIllustration?.src && 
            gameInfoIllustration.complete && 
            gameInfoIllustration.naturalWidth > 0) { 
            if (!gameInfoIllustrationLoaded) { 
                console.log("檢測到遊戲內曲繪已緩存/提前載入:", src); 
                gameInfoIllustrationLoaded = true; 
            } 
        } 
        return; 
    } 
    
    // 開始載入新圖片
    console.log("準備預載新的遊戲內曲繪:", src); 
    gameInfoIllustrationSrc = src; 
    gameInfoIllustrationLoaded = false; 
    gameInfoIllustration = new Image(); 
    
    // 設置載入完成處理函數
    gameInfoIllustration.onload = () => { 
        console.log("遊戲內曲繪載入完成:", src); 
        if (gameInfoIllustrationSrc === src) { 
            gameInfoIllustrationLoaded = true; 
        } else { 
            console.log("遊戲內曲繪載入完成，但目標 src 已改變。忽略此次載入結果。"); 
        } 
    }; 
    
    // 設置載入失敗處理函數
    gameInfoIllustration.onerror = () => { 
        console.warn("遊戲內曲繪失敗:", src); 
        if (gameInfoIllustrationSrc === src) { 
            gameInfoIllustration = null; 
            gameInfoIllustrationSrc = ''; 
        } 
        gameInfoIllustrationLoaded = false; 
    }; 
    
    // 開始載入圖片
    gameInfoIllustration.src = src; 
}
/**
 * 繪製遊戲資訊
 * 在遊戲畫面左上角顯示當前歌曲的曲繪、標題和作者
 */
function drawGameInfo() { 
    if (!ctx || !selectedSongData) return; 
    
    // 定義佈局參數
    const margin = 20, 
          imageSize = 50, 
          textSpacing = 8, 
          titleFontSize = 20, 
          artistFontSize = 14; 
    
    // 獲取當前曲繪路徑
    const currentIllustrationPath = selectedSongData.illustrationPath || ''; 
    
    // 如果曲繪路徑變更，預載新的曲繪
    if (currentIllustrationPath && gameInfoIllustrationSrc !== currentIllustrationPath) { 
        preloadGameInfoIllustration(currentIllustrationPath); 
    } 
    
    // 繪製曲繪
    if (gameInfoIllustration && gameInfoIllustrationLoaded && 
        gameInfoIllustrationSrc === currentIllustrationPath) { 
        try { 
            ctx.globalAlpha = 0.8; 
            ctx.drawImage(gameInfoIllustration, margin, margin, imageSize, imageSize); 
            ctx.globalAlpha = 1.0; 
        } catch (e) { 
            console.error("繪製遊戲內曲繪時出錯:", e, gameInfoIllustration); 
        } 
    } 
    
    // 繪製歌曲標題
    ctx.fillStyle = 'rgba(255, 255, 255, 0.9)'; 
    ctx.textAlign = 'left'; 
    ctx.textBaseline = 'top'; 
    ctx.font = `bold ${titleFontSize}px ${FONT_FAMILY_CANVAS}`; 
    ctx.fillText(selectedSongData.title || '未知', 
                margin + imageSize + textSpacing, margin + 5); 
    
    // 繪製歌曲作者
    ctx.font = `${artistFontSize}px ${FONT_FAMILY_CANVAS}`; 
    ctx.fillStyle = 'rgba(204, 204, 204, 0.9)'; 
    ctx.fillText(selectedSongData.artist || '未知', 
                margin + imageSize + textSpacing, margin + titleFontSize + 8); 
    
    // 重置文字基線
    ctx.textBaseline = 'alphabetic'; 
}

// =============================================================================
// 特效更新與繪製函數
// =============================================================================
/**
 * 更新並繪製打擊特效
 * 管理粒子特效的生命週期和動畫
 * @param {number} currentTime - 當前遊戲時間
 */
function updateAndDrawHitEffects(currentTime) { 
    if (!ctx) return; 
    
    // 過濾掉已經結束生命週期的粒子和特效
    activeHitEffects = activeHitEffects.filter(effect => { 
        effect.particles = effect.particles.filter(particle => 
            currentTime - particle.startTime < particle.lifetime); 
        return effect.particles.length > 0; 
    }); 
    
    // 更新並繪製每個特效的粒子
    activeHitEffects.forEach(effect => { 
        effect.particles.forEach(particle => { 
            // 計算粒子的生命週期和透明度
            const elapsedTime = currentTime - particle.startTime; 
            const lifetimeRatio = elapsedTime / particle.lifetime; 
            
            // 更新粒子位置和旋轉
            particle.x += particle.vx * (1/60); 
            particle.y += particle.vy * (1/60); 
            particle.rotation += particle.angularVelocity * (1/60); 
            
            // 更新透明度
            particle.alpha = Math.max(0, 1.0 - lifetimeRatio); 
            
            // 繪製粒子
            ctx.save(); 
            ctx.fillStyle = particle.color + particle.alpha + ')'; 
            ctx.globalAlpha = particle.alpha; 
            ctx.translate(particle.x, particle.y); 
            ctx.rotate(particle.rotation); 
            
            // 繪製三角形粒子
            const side = particle.size; 
            const height = side * Math.sqrt(3) / 2; 
            ctx.beginPath(); 
            ctx.moveTo(0, -height / 2); 
            ctx.lineTo(-side / 2, height / 2); 
            ctx.lineTo(side / 2, height / 2); 
            ctx.closePath(); 
            ctx.fill(); 
            
            ctx.restore(); 
        }); 
    }); 
    
    // 重置全局透明度
    ctx.globalAlpha = 1.0; 
}
/**
 * 更新並繪製軌道閃光效果
 * 當玩家按下按鍵時顯示的軌道閃光
 * @param {number} currentTime - 當前遊戲時間
 */
function updateAndDrawLaneFlashes(currentTime) { 
    if (!ctx) return; 
    
    // 過濾掉已經結束的閃光效果
    activeLaneFlashes = activeLaneFlashes.filter(flash => 
        currentTime - flash.startTime < flash.duration); 
    
    // 繪製每個軌道的閃光效果
    activeLaneFlashes.forEach(flash => { 
        // 計算閃光的透明度
        const elapsedTime = currentTime - flash.startTime; 
        const alpha = Math.max(0, 1.0 - (elapsedTime / flash.duration)); 
        
        // 獲取軌道的四個角點座標
        const laneIndex = flash.laneIndex; 
        const bottomX1 = getInterpolatedX(laneIndex, JUDGMENT_LINE_Y); 
        const bottomX2 = getInterpolatedX(laneIndex + 1, JUDGMENT_LINE_Y); 
        const topX1 = getInterpolatedX(laneIndex, 0); 
        const topX2 = getInterpolatedX(laneIndex + 1, 0); 
        
        // 創建漸變色
        const gradient = ctx.createLinearGradient(0, JUDGMENT_LINE_Y, 0, 0); 
        gradient.addColorStop(0, COLOR_LANE_FLASH + alpha + ')'); 
        gradient.addColorStop(1, COLOR_LANE_FLASH + '0)'); 
        
        // 繪製閃光梯形
        ctx.fillStyle = gradient; 
        ctx.beginPath(); 
        ctx.moveTo(topX1, 0); 
        ctx.lineTo(topX2, 0); 
        ctx.lineTo(bottomX2, JUDGMENT_LINE_Y); 
        ctx.lineTo(bottomX1, JUDGMENT_LINE_Y); 
        ctx.closePath(); 
        ctx.fill(); 
    }); 
}
/**
 * 更新並繪製環形特效
 * 當玩家成功擊中音符時顯示的擴散環
 * @param {number} currentTime - 當前遊戲時間
 */
function updateAndDrawRingEffects(currentTime) { 
    if (!ctx) return; 
    
    // 過濾掉已經結束的環形特效
    activeRingEffects = activeRingEffects.filter(ring => 
        currentTime - ring.startTime < ring.duration); 
    
    // 繪製每個環形特效
    activeRingEffects.forEach(ring => { 
        // 計算特效的進度和縮放比例
        const elapsedTime = currentTime - ring.startTime; 
        const progress = elapsedTime / ring.duration; 
        const currentScale = RING_EFFECT_START_SCALE + 
            (RING_EFFECT_END_SCALE - RING_EFFECT_START_SCALE) * progress; 
        
        // 計算透明度和尺寸
        const currentAlpha = 1.0 - progress; 
        const currentWidth = ring.startWidth * currentScale; 
        const currentHeight = (ring.startWidth / 2) * currentScale; 
        
        // 繪製環形
        ctx.save(); 
        ctx.globalAlpha = Math.max(0, currentAlpha); 
        ctx.strokeStyle = COLOR_RING_EFFECT + Math.max(0, currentAlpha) + ')'; 
        ctx.lineWidth = RING_EFFECT_LINE_WIDTH; 
        ctx.beginPath(); 
        ctx.ellipse( 
            ring.centerX, 
            ring.centerY, 
            currentWidth / 2, 
            currentHeight / 2, 
            0, 0, 2 * Math.PI 
        ); 
        ctx.stroke(); 
        ctx.restore(); 
    }); 
    
    // 重置全局透明度
    ctx.globalAlpha = 1.0; 
}

// =============================================================================
// 遊戲主迴圈 (Game Loop)
// =============================================================================
/**
 * 遊戲主迴圈
 * 負責更新遊戲狀態和繪製所有遊戲元素
 */
function gameLoop() {
    // 檢查遊戲迴圈是否應該繼續運行
    if (!gameLoopRunning) { 
        console.log("遊戲迴圈已標記停止。"); 
        return; 
    }
    
    // 檢查遊戲是否正在播放
    if (!isPlaying) { 
        console.log("偵測到 isPlaying 為 false，停止遊戲迴圈。"); 
        gameLoopRunning = false; 
        if (gameState === 'PLAYING' || gameState === 'GAME') { 
            console.warn("遊戲迴圈檢測到 isPlaying 為 false，但狀態仍是 GAME/PLAYING，嘗試顯示結果。"); 
        } 
        return; 
    }
    
    // 更新歌曲時間
    if (audioContext && isPlaying && audioSource) { 
        rawElapsedTime = audioContext.currentTime - audioStartTime; 
        currentSongTime = Math.max(0, rawElapsedTime); 
    } else { 
        console.error("遊戲狀態異常：isPlaying 為 true 但 AudioContext 或 AudioSource 丟失！"); 
        gameLoopRunning = false; 
        showScreen('SELECTING'); 
        return; 
    }
    
    // 檢查畫布上下文是否可用
    if (!ctx) { 
        console.error("Canvas context lost!"); 
        gameLoopRunning = false; 
        return; 
    }

    // 1. 繪製背景
    drawGameBackground();

    // 2. 更新音符狀態
    if (isPlaying) { 
        loadedNotes.forEach(note => { 
            if (!note.judged) { 
                // 計算音符出現時間 (原始目標時間 - 考慮速度的總偏移量)
                // 將額外偏移量也考慮速度倍率的影響
                const scaledAdditionalOffset = ADDITIONAL_NOTE_OFFSET_SECONDS / speedMultiplier;
                const appearTime = note.targetTime - noteAppearTimeOffset - scaledAdditionalOffset; 
                
                if (rawElapsedTime >= appearTime) { 
                    // 音符已經應該出現
                    note.isActive = true; 
                    
                    // 計算音符的位置
                    const timeSinceAppearRaw = rawElapsedTime - appearTime; 
                    // 計算時間進度比例，考慮速度倍率
                    // 使用 BASE_NOTE_APPEAR_TIME_OFFSET 和 ADDITIONAL_NOTE_OFFSET_SECONDS 的總和，再除以速度倍率
                    const totalBaseOffset = BASE_NOTE_APPEAR_TIME_OFFSET + ADDITIONAL_NOTE_OFFSET_SECONDS;
                    const scaledTotalOffset = totalBaseOffset / speedMultiplier;
                    const timeProgressRaw = scaledTotalOffset > 0 ? 
                        Math.max(0, timeSinceAppearRaw / scaledTotalOffset) : 1; 
                    
                    // 使用混合緩動函數計算 Y 位置進度
                    const yProgress = LINEAR_MIX_FACTOR * timeProgressRaw + 
                        (1 - LINEAR_MIX_FACTOR) * Math.pow(timeProgressRaw, NOTE_SPEED_EASING_POWER); 
                    
                    // 設置音符的 Y 座標
                    note.y = yProgress * JUDGMENT_LINE_Y; 
                    
                    // 檢查是否錯過了音符
                    if (currentSongTime > note.targetTime + JUDGE_WINDOW_MISS) { 
                        if (!note.judged) { 
                            console.log(`判定: Miss (超時) ID: ${note.id}`); 
                            note.judged = true; 
                            note.judgment = 'Miss'; 
                            note.isActive = false; 
                            lastJudgment = { 
                                text: 'Miss', 
                                time: currentSongTime, 
                                column: note.column 
                            }; 
                            combo = 0; 
                            judgmentCounts.miss++; 
                        } 
                    } 
                } else { 
                    // 音符還沒到出現時間
                    note.isActive = false; 
                    note.y = 0; 
                } 
            } else { 
                // 音符已經被判定
                note.isActive = false; 
            } 
        }); 
    }

    // --- 按順序繪製遊戲元素 ---
    updateAndDrawLaneFlashes(currentSongTime); // 3. Lane Flashes
    drawNotes(); // 4. Active Notes
    updateAndDrawRingEffects(currentSongTime); // 5. Ring Effects
    updateAndDrawHitEffects(currentSongTime); // 6. Particle Effects
    drawJudgmentFeedback(); // 7. Judgment Text
    drawScoreAndCombo(); // 8. Score and Combo UI
    drawGameInfo(); // 9. Game Info UI

    // 10. Request Next Frame
    if (gameLoopRunning) { 
        requestAnimationFrame(gameLoop); 
    } else { 
        console.log("gameLoopRunning 為 false，不請求下一幀。"); 
    }
}

// =============================================================================
// 事件監聽器設定
// =============================================================================
window.addEventListener('keydown', function(event) { if (KEY_MAPPINGS.includes(event.code) || event.code === 'Escape') { /* event.preventDefault(); */ } const keyCode = event.code; if (keyCode === 'Escape') { if (['PLAYING', 'GAME', 'RESULT', 'INTRO', 'LOADING'].includes(gameState)) { console.log("Escape 按下，準備返回選單..."); handleBackToSelectClick(); return; } } const keyIndex = KEY_MAPPINGS.indexOf(keyCode); if (keyIndex !== -1) { if (!keyStates[keyCode]) { keyStates[keyCode] = true; if (isPlaying && gameLoopRunning) { activeLaneFlashes.push({ laneIndex: keyIndex, startTime: currentSongTime, duration: LANE_FLASH_DURATION }); } if (isPlaying && gameLoopRunning && currentSongTime > 0 && baseScorePerPerfect >= 0) { const pressTime = currentSongTime; let bestNote = null; let minTimeDiff = Infinity; loadedNotes.forEach(note => { if (note.column === keyIndex && !note.judged && note.isActive) { const timeDiff = pressTime - note.targetTime; if (Math.abs(timeDiff) < JUDGE_WINDOW_MISS + 0.1) { if (Math.abs(timeDiff) < Math.abs(minTimeDiff)) { minTimeDiff = timeDiff; bestNote = note; } } } }); if (bestNote) { const absTimeDiff = Math.abs(minTimeDiff); let judgmentText = ''; let scoreToAdd = 0; let particleCount = 0; let particleColor = ''; if (absTimeDiff <= JUDGE_WINDOW_PERFECT) { judgmentText = 'Perfect'; scoreToAdd = baseScorePerPerfect; combo++; judgmentCounts.perfect++; particleCount = PARTICLE_COUNT_PERFECT; particleColor = COLOR_PERFECT_PARTICLE; } else if (absTimeDiff <= JUDGE_WINDOW_GREAT) { judgmentText = 'Great'; scoreToAdd = baseScorePerPerfect * 0.5; combo++; judgmentCounts.great++; particleCount = PARTICLE_COUNT_GREAT; particleColor = COLOR_GREAT_PARTICLE; } else if (absTimeDiff <= JUDGE_WINDOW_GOOD) { judgmentText = 'Good'; scoreToAdd = baseScorePerPerfect * 0.3; combo++; judgmentCounts.good++; particleCount = PARTICLE_COUNT_GOOD; particleColor = COLOR_GOOD_PARTICLE; } if (judgmentText) { console.log(`判定: ${judgmentText}(+${scoreToAdd.toFixed(2)}) C:${combo} (T:${minTimeDiff.toFixed(3)}s) ID:${bestNote.id}`); bestNote.judged = true; bestNote.isActive = false; lastJudgment = { text: judgmentText, time: currentSongTime, column: keyIndex }; score += scoreToAdd; maxCombo = Math.max(maxCombo, combo); playKeysound(); const particleOriginX = getInterpolatedX(keyIndex + 0.5, JUDGMENT_LINE_Y); const particleOriginY = JUDGMENT_LINE_Y; const newParticleEffect = { type: judgmentText, particles: [] }; for (let i = 0; i < particleCount; i++) { const angle = Math.random() * Math.PI * 2; const speed = PARTICLE_BASE_SPEED + Math.random() * PARTICLE_RANDOM_SPEED; const lifetime = PARTICLE_MIN_LIFETIME + Math.random() * (PARTICLE_MAX_LIFETIME - PARTICLE_MIN_LIFETIME); const size = PARTICLE_BASE_SIZE + Math.random() * PARTICLE_RANDOM_SIZE; const angularVelocity = (Math.random() - 0.5) * 2 * PARTICLE_ANGULAR_VELOCITY_RANGE; newParticleEffect.particles.push({ x: particleOriginX, y: particleOriginY, vx: Math.cos(angle) * speed, vy: Math.sin(angle) * speed, rotation: Math.random() * Math.PI * 2, angularVelocity: angularVelocity, size: size, color: particleColor, alpha: 1.0, startTime: currentSongTime, lifetime: lifetime }); } activeHitEffects.push(newParticleEffect); const ringCenterX = particleOriginX; const ringCenterY = particleOriginY; const ringStartWidth = getInterpolatedX(keyIndex + 1, JUDGMENT_LINE_Y) - getInterpolatedX(keyIndex, JUDGMENT_LINE_Y); activeRingEffects.push({ centerX: ringCenterX, centerY: ringCenterY, startWidth: ringStartWidth, startTime: currentSongTime, duration: RING_EFFECT_DURATION }); } else { console.log(`空敲或時機過差 (T:${minTimeDiff.toFixed(3)}s) ID:${bestNote.id}`); } } else { console.log(`空敲 Lane ${keyIndex + 1}`); } } } } });
window.addEventListener('keyup', function(event) { const keyCode = event.code; if (KEY_MAPPINGS.includes(keyCode)) { if (keyStates[keyCode]) { keyStates[keyCode] = false; } } });
function handleSongSelect(event) { if (gameState !== 'SELECTING') { console.warn("Attempted song selection while not in SELECTING state."); return; } const songItem = event.currentTarget; const songData = availableSongs.find(song => song.id === songItem.dataset.songId); if (songData) { startGame(songData); } else { console.error("選中的歌曲數據無效！", songItem.dataset); alert("選擇的歌曲資料似乎有問題，請稍後再試。"); } }
let resizeTimeout; window.addEventListener('resize', () => { clearTimeout(resizeTimeout); resizeTimeout = setTimeout(() => { resizeCanvas(); drawGameBackground(); }, 100); });
function handleBackToSelectClick() { console.log(`返回按鈕/Escape 觸發... 當前狀態: ${gameState}`); const currentState = gameState; if (gameStartDelayTimeoutId) { console.log("取消待處理的遊戲開始延遲。"); clearTimeout(gameStartDelayTimeoutId); gameStartDelayTimeoutId = null; } const cleanupAndGoToSelect = () => { console.log("執行清理並返回選單..."); if (isPlaying) { if (audioSource) { try { audioSource.stop(); } catch(e) {console.warn("停止音源時出錯(可能已停止):", e);} audioSource.disconnect(); audioSource = null; } isPlaying = false; } gameLoopRunning = false; isAudioLoading = false; isAudioReady = false; isChartLoading = false; isChartReady = false; audioBuffer = null; chartData = null; loadedNotes = []; totalNotesInChart = 0; baseScorePerPerfect = 0; selectedSongData = null; activeHitEffects = []; activeLaneFlashes = []; activeRingEffects = []; songBgImage = null; isSongBgLoading = false; isSongBgReady = false; gameInfoIllustration = null; gameInfoIllustrationSrc = ''; gameInfoIllustrationLoaded = false; showScreen('SELECTING'); }; switch (currentState) { case 'RESULT': console.log("從結算畫面返回，開始淡出..."); resultScreen.classList.remove('visible'); setTimeout(cleanupAndGoToSelect, 500); break; case 'INTRO': console.log("從 Intro 畫面返回，開始淡出..."); introScreen.classList.remove('visible'); setTimeout(cleanupAndGoToSelect, 500); break; case 'LOADING': console.log("從載入畫面返回..."); cleanupAndGoToSelect(); break; case 'PLAYING': case 'GAME': console.log("從遊戲中返回..."); cleanupAndGoToSelect(); break; case 'SELECTING': console.log("已經在選單畫面，無需操作。"); break; default: console.log(`在 ${currentState} 狀態下觸發返回，未定義明確操作，執行預設清理。`); cleanupAndGoToSelect(); break; } }

// =============================================================================
// 速度控制函數
// =============================================================================
function updateSpeedDisplay() { if (speedDisplay) { speedDisplay.textContent = `x${speedMultiplier.toFixed(2)}`; } }
function increaseSpeed() { if (speedMultiplier < MAX_SPEED_MULTIPLIER) { speedMultiplier = parseFloat((speedMultiplier + SPEED_ADJUST_STEP).toFixed(2)); noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier; updateSpeedDisplay(); console.log(`速度增加到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`); } else { console.log("已達到最大速度"); } }
function decreaseSpeed() { if (speedMultiplier > MIN_SPEED_MULTIPLIER) { speedMultiplier = parseFloat((speedMultiplier - SPEED_ADJUST_STEP).toFixed(2)); speedMultiplier = Math.max(MIN_SPEED_MULTIPLIER, speedMultiplier); noteAppearTimeOffset = BASE_NOTE_APPEAR_TIME_OFFSET / speedMultiplier; updateSpeedDisplay(); console.log(`速度減少到: x${speedMultiplier}, Offset: ${noteAppearTimeOffset.toFixed(3)}s`); } else { console.log("已達到最小速度"); } }

// =============================================================================
// Splash Screen 處理函數
// =============================================================================
function initializeAudioContext() { if (!audioContext) { try { audioContext = new AudioContext(); console.log("AudioContext 初始化成功。"); if (audioContext.state === 'suspended') { console.warn("AudioContext 初始狀態為 suspended，嘗試恢復..."); audioContext.resume().then(() => { console.log("AudioContext 已成功恢復！"); }).catch(err => { console.error("自動恢復 AudioContext 失敗:", err); alert("無法自動啟用音訊。如果遊戲無聲，請嘗試重新載入或檢查瀏覽器設定。"); }); } } catch (e) { console.error("無法創建 AudioContext:", e); alert("無法初始化音訊系統。您的瀏覽器可能不支援或已禁用 Web Audio API。"); } } else if (audioContext.state === 'suspended') { console.warn("AudioContext 處於 suspended 狀態，嘗試恢復..."); audioContext.resume().catch(err => { console.error("恢復已存在的 AudioContext 失敗:", err); alert("無法啟用音訊。請嘗試重新整理頁面或檢查瀏覽器設定。"); }); } else { console.log("AudioContext 已存在且狀態為:", audioContext.state); } }
function handleSplashScreenClick() { console.log("Splash Screen 被點擊。"); initializeAudioContext(); const splashFadeOutDuration = 500; if (splashScreen) { splashScreen.classList.remove('visible'); console.log("開始淡出 Splash Screen..."); } setTimeout(() => { console.log("Splash Screen 淡出完成。"); if (splashScreen) { splashScreen.classList.add('hidden'); } const blackScreenDuration = 300; console.log(`保持黑畫面 ${blackScreenDuration}ms...`); setTimeout(() => { console.log("黑畫面結束，顯示選曲畫面..."); showScreen('SELECTING'); }, blackScreenDuration); }, splashFadeOutDuration); }

// =============================================================================
// 應用程式初始化與啟動
// =============================================================================
async function initializeApp() { console.log("應用程式初始化..."); resizeCanvas(); if (splashScreen) { splashScreen.classList.remove('hidden'); splashScreen.classList.add('visible'); splashScreen.addEventListener('click', handleSplashScreenClick, { once: true }); console.log("Splash Screen 已顯示並設定點擊監聽器。"); } else { console.error("找不到 Splash Screen 元素！啟動流程中斷。"); return; } songListContainer.innerHTML = '<p>正在載入歌曲列表...</p>'; try { const response = await fetch('songlist.json'); if (!response.ok) throw new Error(`無法載入 songlist.json: ${response.statusText}`); availableSongs = await response.json(); console.log(`歌曲列表載入完成，共 ${availableSongs.length} 首歌。`); populateSongList(); } catch (error) { console.error("初始化失敗 (載入歌曲列表時):", error); if (songListContainer) songListContainer.innerHTML = `<p style="color: red;">錯誤：無法載入歌曲列表。<br>${error.message}</p>`; } if (increaseSpeedButton && decreaseSpeedButton) { increaseSpeedButton.addEventListener('click', increaseSpeed); decreaseSpeedButton.addEventListener('click', decreaseSpeed); updateSpeedDisplay(); } else { console.error("無法找到速度控制按鈕元素！"); } }

// Wait for DOM to be ready before initializing
window.addEventListener('DOMContentLoaded', initializeApp);
