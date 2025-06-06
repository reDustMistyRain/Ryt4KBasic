/**
 * convert.js - MIDI to Rhythm Game Chart Converter (原始評分 + 禁止三連軌道/和弦版 v2 - 修正)
 *
 * Uses original scoring, allows two consecutive identical lanes/chord patterns,
 * but heavily penalizes the third consecutive use of either.
 * Fixes ReferenceError in getUpcomingNotes.
 */

const fs = require('fs');
const path = require('path');
const { Midi } = require('@tonejs/midi');

// =====================================================================
// 配置區域 - 添加和弦三連懲罰
// =====================================================================

const INPUT_MIDI_FILE = 'test.mid';
const OUTPUT_JSON_FILE = 'output_chart_original_no_triple_lane_or_chord_v2.json'; // 新文件名
const AUDIO_FILENAME_BASE = path.basename(INPUT_MIDI_FILE, '.mid');

const LANE_COUNT = 4;
const SIMULTANEITY_THRESHOLD = 0.010;
const ANTI_JACK_THRESHOLD = 0.100;
const LANE_HISTORY_LENGTH = 8;
const PATTERN_VARIETY_WEIGHT = 0.8;
const PITCH_WEIGHT = 0.5;
const FORCE_LANE_ROTATION = true;
const MIN_LANE_ROTATION_COUNT = 2;
const LOOKAHEAD_NOTES_COUNT = 8;
// 二連懲罰已移除
const TRIPLE_LANE_REUSE_PENALTY = 10000; // **軌道**三連懲罰
const TRIPLE_PATTERN_REPEAT_PENALTY = 8000; // **和弦模式**三連的懲罰分數
const RANDOMIZE_SIMULTANEOUS = false;

// =====================================================================
// 全局變數
// =====================================================================
let minPitch = 127, maxPitch = 0, pitchRange = 1, pitchStep = 1;
const laneUsageCount = Array(LANE_COUNT).fill(0);
// 移除 simultaneousPatternMemory

// =====================================================================
// 輔助函式
// =====================================================================

// ** Corrected Function Definition **
function getUpcomingNotes(allMidiNotes, startIndex, count) { // Added missing parameters
    const upcomingNotes = [];
    let currentIndex = startIndex; // Now startIndex is defined
    let notesAdded = 0;
    let lastTime = -1;
    while (currentIndex < allMidiNotes.length && notesAdded < count) {
        // Ensure note exists and has time property
        const note = allMidiNotes[currentIndex];
        if (!note || typeof note.time === 'undefined') {
            console.warn(`Invalid note found at index ${currentIndex} in getUpcomingNotes`);
            currentIndex++;
            continue;
        }

        if (lastTime === -1 || Math.abs(note.time - lastTime) >= SIMULTANEITY_THRESHOLD) {
            upcomingNotes.push(note);
            lastTime = note.time;
            notesAdded++;
        }
        currentIndex++;
    }
    return upcomingNotes;
}
// ** End of Correction **


function generatePatternKey(columns) {
    // 返回排序後的鍵，或null/空字符串表示單音符或無音符
    if (!columns || columns.length <= 1) {
        return null;
    }
    return columns.sort((a, b) => a - b).join('-');
}
// 移除 checkPatternRepetition

/**
 * 計算軌道分數 (增加和弦三連懲罰的考慮)
 */
function calculateLaneScore(
    lane,
    currentTime,
    noteData,
    usedLanesInCurrentEvent,
    upcomingNotes,
    previousEventLanes,
    secondPreviousEventLanes,
    lastNoteTimeInLane,
    laneUsageOrder,
    recentLanePattern,
    // 新增和弦模式參數
    currentPotentialPatternKey,
    previousPatternKey,
    secondPreviousPatternKey
) {
    if (usedLanesInCurrentEvent.includes(lane)) {
        return -Infinity;
    }

    let score = 0;
    const noteMidi = noteData.midi;

    // 1. 連打避免
    const timeSinceLast = currentTime - lastNoteTimeInLane;
    if (timeSinceLast < ANTI_JACK_THRESHOLD) {
        return -100000;
    } else {
        score += Math.min(timeSinceLast, 1.0) * 20;
    }

    // 2. **軌道**三連懲罰
    if (previousEventLanes.includes(lane) && secondPreviousEventLanes.includes(lane)) {
        score -= TRIPLE_LANE_REUSE_PENALTY;
    }

    // 3. **和弦模式**三連懲罰
    if (currentPotentialPatternKey &&
        currentPotentialPatternKey === previousPatternKey &&
        currentPotentialPatternKey === secondPreviousPatternKey)
    {
        score -= TRIPLE_PATTERN_REPEAT_PENALTY;
    }

    // 4. 強制輪換懲罰 (長期)
    if (FORCE_LANE_ROTATION && laneUsageOrder.length >= MIN_LANE_ROTATION_COUNT) {
        const lastUseIndex = laneUsageOrder.lastIndexOf(lane);
        if (lastUseIndex !== -1) {
            const uniqueLanesSinceLastUse = new Set(laneUsageOrder.slice(lastUseIndex + 1)).size;
            if (uniqueLanesSinceLastUse < MIN_LANE_ROTATION_COUNT) {
                score -= 600 * (MIN_LANE_ROTATION_COUNT - uniqueLanesSinceLastUse + 1);
            }
        }
    }

    // 5. 最近模式懲罰 (手型 - 基於軌道)
    if (recentLanePattern.includes(lane)) {
        const patternIndex = recentLanePattern.lastIndexOf(lane);
        const recencyPenalty = (recentLanePattern.length - patternIndex) * 60;
        score -= recencyPenalty * PATTERN_VARIETY_WEIGHT;
    }

    // 6. 音高匹配獎勵
    if (pitchStep > 0) {
        const idealLane = Math.max(0, Math.min(LANE_COUNT - 1,
            Math.floor((noteData.midi - minPitch) / pitchStep)));
        const pitchMatchBonus = 1 - (Math.abs(lane - idealLane) / LANE_COUNT);
        score += pitchMatchBonus * 50 * PITCH_WEIGHT;
    }

    // 7. 軌道平衡
    const totalUsage = laneUsageCount.reduce((sum, count) => sum + count, 1);
    const averageUsage = totalUsage / LANE_COUNT;
    if (laneUsageCount[lane] > averageUsage) {
        score -= (laneUsageCount[lane] / averageUsage - 1) * 50;
    } else {
        score += (1 - laneUsageCount[lane] / averageUsage) * 25;
    }

    // 8. 前瞻分析
    if (upcomingNotes && upcomingNotes.length > 0) {
        let futureConflictPenalty = 0;
        upcomingNotes.forEach((futureNote, index) => {
             // Add safety check for futureNote
             if (!futureNote || typeof futureNote.midi === 'undefined' || typeof futureNote.time === 'undefined') return;
             const futureIdealLane = pitchStep > 0 ? Math.max(0, Math.min(LANE_COUNT - 1,
                 Math.floor((futureNote.midi - minPitch) / pitchStep))) : lane;
             if (futureIdealLane === lane) {
                 const timeUntilFutureNote = futureNote.time - currentTime;
                 if (timeUntilFutureNote < ANTI_JACK_THRESHOLD * 2.0 && timeUntilFutureNote >= 0) { // Ensure positive time diff
                     futureConflictPenalty += (150 / (index + 1)) * (1 - timeUntilFutureNote / (ANTI_JACK_THRESHOLD * 2.0));
                 }
             }
         });
        score -= futureConflictPenalty;
    }

    return score;
}

/**
 * 分配同時音符的策略
 */
function assignSimultaneousNotes(
    simultaneousNotes,
    currentTime,
    upcomingNotes,
    previousEventLanes,
    secondPreviousEventLanes,
    lastNoteTimeInLaneArray,
    laneUsageOrder,
    recentLanePattern,
    previousPatternKey,
    secondPreviousPatternKey
) {
    const assignment = {};
    const notesToAssignEntries = [...simultaneousNotes.entries()];
    const usedLanesThisEvent = [];
    const potentialAssignment = {}; // 臨時存儲當前可能的分配

    while (notesToAssignEntries.length > 0) {
        let bestOverallChoice = { noteIndex: -1, lane: -1, score: -Infinity };

        for (const [noteIndex, note] of notesToAssignEntries) {
            let bestLaneForThisNote = { lane: -1, score: -Infinity };

            for (let lane = 0; lane < LANE_COUNT; lane++) {
                if (!usedLanesThisEvent.includes(lane)) {
                    // 預測模式
                    potentialAssignment[noteIndex] = lane;
                    // Generate potential key based on *all* notes being assigned *if* this choice is made
                    const potentialLanesForPattern = [...usedLanesThisEvent];
                    notesToAssignEntries.forEach(([idx, _]) => {
                         // Add the currently assigned lane for this note, or the potential lane if it's the one being tested
                         potentialLanesForPattern.push(idx === noteIndex ? lane : potentialAssignment[idx]);
                    });
                    // Filter out undefined lanes (notes not yet assigned in this loop iteration)
                    const definedPotentialLanes = potentialLanesForPattern.filter(l => typeof l !== 'undefined');
                    const potentialKey = generatePatternKey(definedPotentialLanes);
                    delete potentialAssignment[noteIndex]; // Clean up temporary assignment

                    const score = calculateLaneScore(
                        lane, currentTime, note, usedLanesThisEvent, upcomingNotes,
                        previousEventLanes, secondPreviousEventLanes,
                        lastNoteTimeInLaneArray[lane],
                        laneUsageOrder, recentLanePattern,
                        potentialKey, // Use the more accurately predicted potential key
                        previousPatternKey,
                        secondPreviousPatternKey
                    );
                    if (score > bestLaneForThisNote.score) {
                        bestLaneForThisNote = { lane, score };
                    }
                }
            }
             if (bestLaneForThisNote.score > bestOverallChoice.score) {
                 bestOverallChoice = { noteIndex, lane: bestLaneForThisNote.lane, score: bestLaneForThisNote.score };
             } else if (bestLaneForThisNote.score === bestOverallChoice.score && bestOverallChoice.score > -Infinity) {
                  if (bestLaneForThisNote.lane < bestOverallChoice.lane) {
                       bestOverallChoice = { noteIndex, lane: bestLaneForThisNote.lane, score: bestLaneForThisNote.score };
                  }
             }
        }

        if (bestOverallChoice.noteIndex !== -1 && bestOverallChoice.lane !== -1) {
            const { noteIndex, lane } = bestOverallChoice;
            assignment[noteIndex] = lane; // Final assignment for this iteration
            potentialAssignment[noteIndex] = lane; // Keep track for pattern prediction in next loops
            usedLanesThisEvent.push(lane);
             const indexToRemove = notesToAssignEntries.findIndex(([idx, _]) => idx === noteIndex);
             if (indexToRemove !== -1) notesToAssignEntries.splice(indexToRemove, 1);
        } else { /* ... 緊急處理 ... */
             if (notesToAssignEntries.length > 0) {
                console.error(`錯誤：時間 ${currentTime.toFixed(3)} 無法為剩餘 ${notesToAssignEntries.length} 個音符找到分配方案！`);
                const remainingIndices = notesToAssignEntries.map(([idx, _]) => idx);
                 const remainingLanes = Array.from({length: LANE_COUNT}, (_, k) => k).filter(l => !usedLanesThisEvent.includes(l));
                 remainingIndices.forEach((noteIndex, i) => {
                     if (i < remainingLanes.length) {
                         const fallbackLane = remainingLanes[i];
                         assignment[noteIndex] = fallbackLane;
                         usedLanesThisEvent.push(fallbackLane);
                         console.warn(`   緊急分配 Note idx ${noteIndex} to Lane ${fallbackLane}`);
                     } else {
                          console.error(`   無法分配 Note idx ${noteIndex}, 軌道不足.`);
                     }
                 });
                notesToAssignEntries.length = 0;
            }
         }
    }
    return assignment;
}

// =====================================================================
// 主轉換函式
// =====================================================================
async function convertMidiToJson_OriginalLogicNoTripleLaneOrChord() {
    try {
        console.log(`[配置] 原始評分 + 禁止三連軌道/和弦 (軌道懲罰: ${TRIPLE_LANE_REUSE_PENALTY}, 模式懲罰: ${TRIPLE_PATTERN_REPEAT_PENALTY})`);

        // 步驟 1-6:
        console.log(`讀取 MIDI 文件: ${INPUT_MIDI_FILE}...`);
        const midiData = fs.readFileSync(path.join(__dirname, INPUT_MIDI_FILE));
        console.log("解析 MIDI 數據...");
        const midi = new Midi(midiData);
        const outputJson = {
             metadata: {
                 title: midi.header.name || AUDIO_FILENAME_BASE,
                 artist: "未知",
                 charter: "自動轉換 (原始評分+禁止三連軌道/和弦 v2)", // Updated
                 difficulty_name: "轉換",
                 difficulty_level: 0,
                 audio_filename: AUDIO_FILENAME_BASE + '.mp3',
                 preview_start_time: 0,
                 global_offset_ms: 0
             },
             timing_points: [],
             notes: []
        };
        // BPM 處理
         if (midi.header.tempos.length > 0) {
             midi.header.tempos.sort((a, b) => a.ticks - b.ticks);
             if (midi.header.tempos[0].ticks > 0 && midi.header.tempos[0].bpm) {
                  outputJson.timing_points.push({ time: 0, bpm: midi.header.tempos[0].bpm });
             }
             midi.header.tempos.forEach(tempo => {
                  if (tempo.bpm && !outputJson.timing_points.some(tp => Math.abs(tp.time - tempo.time) < 0.001)) {
                      outputJson.timing_points.push({ time: tempo.time, bpm: tempo.bpm });
                  }
              });
             outputJson.timing_points.sort((a, b) => a.time - b.time);
             outputJson.timing_points = outputJson.timing_points.filter((tp, index, arr) =>
                 index === arr.length - 1 || Math.abs(tp.time - arr[index + 1].time) >= 0.001
              );
         }
         if (outputJson.timing_points.length === 0) {
              outputJson.timing_points.push({ time: 0, bpm: 120.0 });
          }
        const allMidiNotes = [];
        midi.tracks.forEach(track => track.notes.forEach(note => allMidiNotes.push({ time: note.time, midi: note.midi, duration: note.duration, track: track.channel })));
        console.log(`總共讀取 ${allMidiNotes.length} 個音符。`);
        allMidiNotes.sort((a, b) => (Math.abs(a.time - b.time) < SIMULTANEITY_THRESHOLD / 2) ? a.midi - b.midi : a.time - b.time);
        if (allMidiNotes.length > 0) {
             allMidiNotes.forEach(note => { minPitch = Math.min(minPitch, note.midi); maxPitch = Math.max(maxPitch, note.midi); });
             if (minPitch === maxPitch) maxPitch += 1;
             pitchRange = maxPitch - minPitch;
             pitchStep = pitchRange > 0 ? pitchRange / LANE_COUNT : 1;
             console.log(`音高範圍: ${minPitch} - ${maxPitch}, pitchStep: ${pitchStep.toFixed(2)}`);
         } else {
              console.warn("警告：未找到任何音符！");
              minPitch = 60; maxPitch = 61; pitchRange = 1; pitchStep = 1 / LANE_COUNT;
          }

        // 步驟 7: 初始化狀態
        const gameNotes = [];
        const lastNoteTimeInLaneArray = Array(LANE_COUNT).fill(-Infinity);
        const laneHistory = Array(LANE_COUNT).fill().map(() => []);
        let recentLanePattern = [];
        let laneUsageOrder = [];
        let previousEventLanes = [];
        let secondPreviousEventLanes = [];
        let previousPatternKey = null;
        let secondPreviousPatternKey = null;

        // 步驟 8: 處理音符
        for (let i = 0; i < allMidiNotes.length; /* i controlled inside */) {
            const currentTime = allMidiNotes[i].time;
            const currentTimeKey = currentTime.toFixed(4);

            // 8.1: 識別同時音符組
            const simultaneousNotes = [allMidiNotes[i]];
            let lookAheadIndex = i + 1;
            while (lookAheadIndex < allMidiNotes.length && Math.abs(allMidiNotes[lookAheadIndex].time - currentTime) < SIMULTANEITY_THRESHOLD) {
                // Ensure notes are valid before pushing
                if (allMidiNotes[lookAheadIndex] && typeof allMidiNotes[lookAheadIndex].time !== 'undefined') {
                    simultaneousNotes.push(allMidiNotes[lookAheadIndex]);
                } else {
                     console.warn(`Skipping invalid note during simultaneity check at index ${lookAheadIndex}`);
                }
                lookAheadIndex++;
            }

            // 8.2: 獲取未來音符
            const upcomingNotes = getUpcomingNotes(allMidiNotes, lookAheadIndex, LOOKAHEAD_NOTES_COUNT); // Corrected Call

            // 8.3: 排序並可能截斷音符
            simultaneousNotes.sort((a, b) => a.midi - b.midi);
            if (simultaneousNotes.length > LANE_COUNT) {
                console.warn(`警告：時間 ${currentTimeKey} 同時音符 (${simultaneousNotes.length}) > ${LANE_COUNT}，丟棄！`);
                simultaneousNotes.splice(LANE_COUNT);
            }

            // 8.4: 核心分配
            let assignedColumns = {};
            if (simultaneousNotes.length === 1) {
                // --- 單個音符 ---
                const note = simultaneousNotes[0];
                const laneScores = [];
                for (let lane = 0; lane < LANE_COUNT; lane++) {
                    const score = calculateLaneScore(
                        lane, currentTime, note, [], upcomingNotes,
                        previousEventLanes, secondPreviousEventLanes,
                        lastNoteTimeInLaneArray[lane], laneUsageOrder, recentLanePattern,
                        null, previousPatternKey, secondPreviousPatternKey
                    );
                    laneScores.push({ lane, score });
                }
                laneScores.sort((a, b) => b.score - a.score);
                 if (laneScores.length > 0 && laneScores[0].score > -Infinity) {
                     assignedColumns[0] = laneScores[0].lane;
                      if (laneScores[0].score < -TRIPLE_LANE_REUSE_PENALTY / 2) { /* log warning */ }
                 } else { /* 緊急處理 */
                      console.error(`錯誤：時間 ${currentTimeKey} 無法為單音符 ${note.midi} 找到有效軌道！`);
                      laneScores.sort((a, b) => b.score - a.score); // Re-sort just in case
                      if (laneScores.length > 0) {
                           assignedColumns[0] = laneScores[0].lane;
                           console.warn(`   緊急選擇得分最低 (${laneScores[0].score.toFixed(1)}) 的軌道 ${laneScores[0].lane}`);
                      } else {
                           const fallbackLane = laneUsageCount.indexOf(Math.min(...laneUsageCount));
                           assignedColumns[0] = fallbackLane;
                           console.warn(`   緊急選擇使用次數最少的軌道 ${fallbackLane}`);
                      }
                  }
            } else {
                // --- 同時音符 ---
                assignedColumns = assignSimultaneousNotes(
                    simultaneousNotes, currentTime, upcomingNotes,
                    previousEventLanes, secondPreviousEventLanes,
                    lastNoteTimeInLaneArray, laneUsageOrder, recentLanePattern,
                    previousPatternKey, secondPreviousPatternKey
                );
            }

            // 8.5: 獲取最終模式鍵
            const assignedLanesArray = Object.values(assignedColumns);
            const currentPatternKey = generatePatternKey(assignedLanesArray);

            // 檢查實際發生的三連模式
            if (currentPatternKey &&
                currentPatternKey === previousPatternKey &&
                currentPatternKey === secondPreviousPatternKey)
            {
                 console.warn(`   -> 時間 ${currentTimeKey}: 檢測到連續第三次使用和弦模式 "${currentPatternKey}" (可能因必要性)`);
            }

            // 8.6: 創建音符並更新狀態
            const currentEventLanesUsedSet = new Set();
            simultaneousNotes.forEach((note, noteIndexInGroup) => {
                if (assignedColumns[noteIndexInGroup] !== undefined) {
                    const finalColumn = assignedColumns[noteIndexInGroup];
                    gameNotes.push({ targetTime: currentTime, column: finalColumn, type: 'tap', midiPitch: note.midi });
                    // 更新狀態
                    lastNoteTimeInLaneArray[finalColumn] = currentTime;
                    laneUsageCount[finalColumn]++;
                    laneHistory[finalColumn].push({ time: currentTime, midi: note.midi });
                    if (laneHistory[finalColumn].length > LANE_HISTORY_LENGTH) laneHistory[finalColumn].shift();
                    recentLanePattern.push(finalColumn);
                    if (recentLanePattern.length > LANE_HISTORY_LENGTH) recentLanePattern.shift();
                    laneUsageOrder.push(finalColumn);
                    if (laneUsageOrder.length > LANE_COUNT * 3) laneUsageOrder.shift();
                    currentEventLanesUsedSet.add(finalColumn);
                } else { /* 警告 */
                     console.warn(`警告: 時間 ${currentTimeKey} 的音符 ${note.midi} (組內索引 ${noteIndexInGroup}) 未被分配!`);
                 }
            });

            // 8.7: 更新時間窗口狀態
            const currentEventLanes = [...currentEventLanesUsedSet];
            secondPreviousEventLanes = previousEventLanes;
            previousEventLanes = currentEventLanes;
            secondPreviousPatternKey = previousPatternKey;
            previousPatternKey = currentPatternKey;

            // 8.8: 前進
            i = lookAheadIndex;
        } // end main for loop

        // 步驟 9-10:
        gameNotes.sort((a, b) => (a.targetTime !== b.targetTime) ? a.targetTime - b.targetTime : a.column - b.column);
        outputJson.notes = gameNotes;
        fs.writeFileSync(path.join(__dirname, OUTPUT_JSON_FILE), JSON.stringify(outputJson, null, 2));
        console.log(`\n轉換成功！JSON 譜面已儲存至: ${path.join(__dirname, OUTPUT_JSON_FILE)}`);
        console.log(`共轉換 ${outputJson.notes.length} 個遊戲音符。`);

        // 步驟 11: 分析
        analyzeChartQuality_NoTripleLaneOrChord(gameNotes, ANTI_JACK_THRESHOLD, SIMULTANEITY_THRESHOLD);

    } catch (error) {
        console.error("\nMIDI 轉換過程中發生嚴重錯誤:", error);
        if (error.stack) console.error(error.stack);
    }
}


/**
 * 分析譜面質量 (更新版，同時檢查軌道和模式的三連情況)
 */
function analyzeChartQuality_NoTripleLaneOrChord(gameNotes, antiJackThreshold, simultaneityThreshold) {
    if (!gameNotes || gameNotes.length === 0) { /* ... */ return; }
    gameNotes.sort((a, b) => a.targetTime - b.targetTime);

    let jackCount = 0;
    let maxJackChain = 0;
    let currentJackChain = 0;
    const laneNoteCount = Array(LANE_COUNT).fill(0);
    const laneLastNoteTimeAnalyzed = Array(LANE_COUNT).fill(-Infinity);
    let tripleLaneOccurrences = 0;
    let triplePatternOccurrences = 0;

    let lastTime = -1;
    let notesAtTime = {};
    const distinctTimes = [];

    gameNotes.forEach(note => {
        // Ensure notes are valid before processing
        if (!note || typeof note.targetTime === 'undefined' || typeof note.column === 'undefined') {
             console.warn("Invalid note encountered during analysis:", note);
             return;
        }
        const timeKey = note.targetTime.toFixed(5);
        if (!notesAtTime[timeKey]) {
            notesAtTime[timeKey] = [];
            distinctTimes.push(note.targetTime);
        }
        notesAtTime[timeKey].push(note);
    });
    distinctTimes.sort((a, b) => a - b);

    let prevLanes = new Set();
    let prev2Lanes = new Set();
    let prevPatternKey = null;
    let prev2PatternKey = null;

    for (const time of distinctTimes) {
        const timeKey = time.toFixed(5);
        const notes = notesAtTime[timeKey];
         if (!notes) continue; // Skip if time key somehow doesn't exist

        const currentLanes = new Set(notes.map(n => n.column));
        const currentPatternKey = generatePatternKey([...currentLanes]);

        // 檢查軌道三連
        const forbiddenLanes = [...prevLanes].filter(l => prev2Lanes.has(l));
        const actualTripleLanes = [...currentLanes].filter(l => forbiddenLanes.includes(l));
        if (actualTripleLanes.length > 0) {
            tripleLaneOccurrences += actualTripleLanes.length;
        }

        // 檢查模式三連
        if (currentPatternKey &&
            currentPatternKey === prevPatternKey &&
            currentPatternKey === prev2PatternKey)
        {
            triplePatternOccurrences++;
        }

        // 更新狀態
        prev2Lanes = new Set(prevLanes);
        prevLanes = new Set(currentLanes);
        prev2PatternKey = prevPatternKey;
        prevPatternKey = currentPatternKey;

        // 內部連打分析
        notes.forEach(note => {
            const lane = note.column;
            laneNoteCount[lane]++;
            const timeSinceLastInLane = note.targetTime - laneLastNoteTimeAnalyzed[lane];
             if (laneLastNoteTimeAnalyzed[lane] > -Infinity) {
                 if (timeSinceLastInLane < antiJackThreshold) {
                     jackCount++; currentJackChain++; maxJackChain = Math.max(maxJackChain, currentJackChain);
                 } else {
                     currentJackChain = 0;
                 }
             }
              laneLastNoteTimeAnalyzed[lane] = note.targetTime;
        });
    }

    const totalNotes = gameNotes.length;
    const jackPercentage = totalNotes > 0 ? (jackCount / totalNotes * 100).toFixed(2) : 0;
    const laneDistribution = laneNoteCount.map(count => totalNotes > 0 ? (count / totalNotes * 100).toFixed(2) + '%' : '0.00%');

    console.log('\n譜面質量分析 (原始評分+禁止三連軌道/和弦版):');
    console.log(`總音符數: ${totalNotes}`);
    console.log(`連打數量 (< ${antiJackThreshold}s): ${jackCount} (${jackPercentage}%)`);
    console.log(`最長連打鏈: ${maxJackChain} 個音符`);
    console.log(`軌道分佈: ${laneDistribution.join(' | ')}`);
    console.log(`實際發生軌道三連的音符數: ${tripleLaneOccurrences}`);
    console.log(`實際發生和弦模式三連的次數: ${triplePatternOccurrences}`);

    let evaluation = [];
    if (jackPercentage < 5) evaluation.push("連打控制極佳");
    else if (jackPercentage < 15) evaluation.push("連打比例合理");
    else evaluation.push("連打可能偏多");
    if (tripleLaneOccurrences === 0) evaluation.push("未出現軌道三連");
    else evaluation.push(`出現 ${tripleLaneOccurrences} 次軌道三連(必要/懲罰不足)`);
    if (triplePatternOccurrences === 0) evaluation.push("未出現和弦模式三連");
    else evaluation.push(`出現 ${triplePatternOccurrences} 次和弦模式三連(必要/懲罰不足)`);
    const minUsage = Math.min(...laneNoteCount);
    const maxUsage = Math.max(...laneNoteCount);
     if (totalNotes > LANE_COUNT * 5 && (maxUsage / (totalNotes / LANE_COUNT)) > 1.6) {
        evaluation.push("軌道平衡有待改善");
    } else if (totalNotes > 0) {
        evaluation.push("軌道分佈較均衡");
    }
    console.log(`評價: ${evaluation.join(', ')}`);
}


// =====================================================================
// 執行轉換
// =====================================================================
convertMidiToJson_OriginalLogicNoTripleLaneOrChord();